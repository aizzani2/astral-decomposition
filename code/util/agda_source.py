"""
Reading Agda source text: where a declaration is, its clauses, and the
`begin ... ∎` chains in them.

Everything here works on the text, so it can find a declaration in a file
that does not load (a sketch, a model's attempt). It handles what library
code does: declarations nested in `module _ ... where` blocks, multi-line
signatures, implicit patterns (`f {n = zero} x = ...`), `rewrite` and `with`
clauses, literate Markdown.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from util.sketch_ops import mask_comments

# Unsolved metavariables as Agda prints them: `_x_7`, `?0`.
META_RE = re.compile(r"(?<![\w])_\w*?\d+\b|\?\d+")
# Agda words are delimited by whitespace and brackets.
WORD_RE = re.compile(r"[^\s(){}]+")
# A name Agda printed qualified (`Data.Empty.⊥`): not in scope unqualified.
QUALIFIED_RE = re.compile(r"(?<![^\s(){}])[A-Z][^\s(){}.]*\.[^\s(){}]")


def split_equation(statement: str) -> tuple[str, str]:
    """Split `lhs ≡ rhs` at the top-level `≡`."""

    depth = 0

    for index, char in enumerate(statement):
        if char in "({[":
            depth += 1
        elif char in ")}]":
            depth -= 1
        elif char == "≡" and depth == 0:
            return statement[:index].strip(), statement[index + 1:].strip()

    raise ValueError(f"Not an equation: {statement!r}")


# ---------------------------------------------------------------------------
# Locating clauses
# ---------------------------------------------------------------------------


@dataclass
class ChainStep:
    """One `x REL⟨ p ⟩ y` step of a `begin ... ∎` chain, with source offsets."""

    lhs: str
    rhs: str
    relation: str
    reversed: bool
    justification: str                        # "" for a `REL⟨⟩` step
    span: tuple[int, int] | None = None       # the justification, in the file


@dataclass
class Clause:
    lhs: str
    rhs: str
    rhs_span: tuple[int, int] | None  # None: nothing to take apart
    note: str = ""
    chain: list[ChainStep] | None = None
    local_names: set[str] = field(default_factory=set)  # declared in its where block


def indentation(line: str) -> int:
    return len(line) - len(line.lstrip())


def signature_index(lines: list[str], name: str, line: int | None = None) -> int:
    """
    Index of the line holding `name`'s type signature, at any indentation
    (declarations inside `module _ ...` blocks are indented). `line` (1-based,
    e.g. from a dataset's ranges) picks between several matches.
    """

    pattern = re.compile(rf"^\s*{re.escape(name)}\s*:(?!:)")
    matches = [i for i, text in enumerate(lines) if pattern.match(text)]

    if not matches:
        raise ValueError(f"No type signature for {name}.")

    if line is None:
        return matches[0]

    return min(matches, key=lambda i: abs(i - (line - 1)))


def parse_clauses(source: str, name: str, line: int | None = None) -> tuple[str, list[Clause]]:
    """The signature and clauses of the declaration `name`."""

    masked = mask_comments(source)
    lines = masked.splitlines(keepends=True)
    offsets = [0]

    for text in lines:
        offsets.append(offsets[-1] + len(text))

    at = signature_index(lines, name, line)
    column = indentation(lines[at])

    clauses: list[Clause] = []
    signature_lines = [lines[at]]
    index = at + 1

    while index < len(lines):
        text = lines[index]

        if not text.strip():
            index += 1
            continue

        if indentation(text) > column:
            if not clauses:   # the signature continues
                signature_lines.append(text)
            index += 1
            continue

        if indentation(text) < column:
            break

        stripped = text.strip()
        head = re.split(r"[\s(){}]", stripped, maxsplit=1)[0]

        if head != name and not stripped.startswith("..."):
            break   # the next declaration at this level

        # The clause runs until the next line at or left of its own column.
        end = index + 1
        while end < len(lines) and (not lines[end].strip() or indentation(lines[end]) > column):
            end += 1

        block_start, block_end = offsets[index], offsets[end]
        block = masked[block_start:block_end]
        # The first free-standing `=` outside brackets ends the left-hand side
        # (`f {n = zero} x = ...`), even when the right-hand side starts on
        # the next line. A `rewrite` sits before it and is part of the left;
        # a `with` header has none, and its `... | p = rhs` continuations are
        # ordinary clauses.
        equals = _clause_equals(block)
        lhs = block[: equals[0]] if equals else block

        if equals is None and re.search(r"\swith\s", block):
            clauses.append(Clause(" ".join(block.split()), "", None, "with header"))
        elif equals is None:
            clauses.append(Clause(" ".join(lhs.split()), "", None, "absurd clause"))
        else:
            rhs_start = block_start + equals[1]
            rhs_start += len(masked[rhs_start:block_end]) - len(masked[rhs_start:block_end].lstrip())
            where = re.search(r"^\s+where\b", masked[rhs_start:block_end], re.MULTILINE)
            rhs_end = rhs_start + where.start() if where else block_end
            rhs_end = rhs_start + len(masked[rhs_start:rhs_end].rstrip())
            local = set(re.findall(
                r"^\s+([^\s(){};:]+)\s*:(?!:)", masked[rhs_end:block_end], re.MULTILINE
            )) if where else set()
            clauses.append(Clause(
                " ".join(lhs.split()),
                " ".join(masked[rhs_start:rhs_end].split()),
                (rhs_start, rhs_end),
                "where-block not taken apart" if where else "",
                parse_chain(masked[rhs_start:rhs_end], rhs_start),
                local,
            ))

        index = end

    signature = " ".join("".join(signature_lines).split())

    return signature, clauses


def _clause_equals(block: str) -> tuple[int, int] | None:
    """Span of the first `=` token at bracket depth 0, if any."""

    depth = 0

    for match in re.finditer(r"[({\[]|[)}\]]|(?<=\s)=(?=\s)", block):
        token = match.group(0)
        if token in "({[":
            depth += 1
        elif token in ")}]":
            depth = max(0, depth - 1)
        elif depth == 0:
            return match.span()

    return None


def declaration_span(source: str, name: str, line: int | None = None) -> tuple[int, int, int, int]:
    """
    Offsets of a declaration in `source`: (start of its signature line,
    start of its first clause line, end of its last clause, its column).
    With no clauses, the second and third are the end of the signature.
    """

    masked = mask_comments(source)
    lines = masked.splitlines(keepends=True)
    offsets = [0]

    for text in lines:
        offsets.append(offsets[-1] + len(text))

    start = signature_index(lines, name, line)
    column = indentation(lines[start])
    index = start + 1

    # The signature runs on while lines are indented past its column.
    while index < len(lines) and (not lines[index].strip() or indentation(lines[index]) > column):
        index += 1

    body = last = index

    while index < len(lines):
        text = lines[index]

        if not text.strip() or indentation(text) > column:
            index += 1
            continue

        head = re.split(r"[\s(){}]", text.strip(), maxsplit=1)[0]

        if indentation(text) < column or (head != name and not text.strip().startswith("...")):
            break

        index += 1
        while index < len(lines) and (not lines[index].strip() or indentation(lines[index]) > column):
            index += 1
        last = index

    # Trailing blank lines belong to whatever follows.
    while last > body and not lines[last - 1].strip():
        last -= 1

    if body == last:   # no clauses: everything ends with the signature
        while body > start + 1 and not lines[body - 1].strip():
            body -= 1
        return offsets[start], offsets[body], offsets[body], column

    return offsets[start], offsets[body], offsets[last], column


_BEGIN_RE = re.compile(r"^begin(?:-[\w-]+)?$")
_STEP_OPEN_RE = re.compile(r"^(\S+?)(˘?)⟨$")     # ≡⟨  ≈˘⟨  ≤⟨
_STEP_DEF_RE = re.compile(r"^(\S+?)⟨⟩$")         # ≡⟨⟩


def parse_chain(text: str, base: int) -> list[ChainStep] | None:
    """
    Read `begin e₀ R⟨ p ⟩ e₁ R⟨⟩ e₂ ... eₙ ∎` into steps, or None if the
    right-hand side is not such a chain. `base` is the text's offset in the
    file, so each justification's span can be replaced later.
    """

    tokens = [(m.group(0), m.start(), m.end()) for m in re.finditer(r"\S+", text)]

    if len(tokens) < 4 or not _BEGIN_RE.match(tokens[0][0]) or tokens[-1][0] != "∎":
        return None

    def depth_change(token: str) -> int:
        return sum(token.count(c) for c in "({[") - sum(token.count(c) for c in ")}]")

    def joined(span_tokens: list[tuple[str, int, int]]) -> str:
        return " ".join(" ".join(text[t[1]:t[2]] for t in span_tokens).split())

    expressions: list[list[tuple[str, int, int]]] = [[]]
    # (relation, reversed, justification tokens or None for REL⟨⟩)
    operators: list[tuple[str, bool, list[tuple[str, int, int]] | None]] = []
    depth = 0
    index = 1

    while index < len(tokens) - 1:
        token = tokens[index]
        opened = _STEP_OPEN_RE.match(token[0])
        definitional = _STEP_DEF_RE.match(token[0])

        if depth == 0 and definitional:
            operators.append((definitional.group(1), False, None))
            expressions.append([])
            index += 1
            continue

        if depth == 0 and opened:
            relation, reverse_mark = opened.group(1), opened.group(2)
            justification: list[tuple[str, int, int]] = []
            inner = 0
            index += 1

            while index < len(tokens) - 1:
                inner_token = tokens[index]
                if inner == 0 and inner_token[0] in ("⟩", "⟨"):
                    break
                justification.append(inner_token)
                inner += depth_change(inner_token[0])
                index += 1
            else:
                return None

            closing = tokens[index][0]
            operators.append((relation, bool(reverse_mark) or closing == "⟨", justification))
            expressions.append([])
            index += 1
            continue

        expressions[-1].append(token)
        depth += depth_change(token[0])
        index += 1

    if not operators or any(not e for e in expressions):
        return None

    steps: list[ChainStep] = []

    for position, (relation, reverse, justification) in enumerate(operators):
        span = None
        if justification:
            span = (base + justification[0][1], base + justification[-1][2])
        steps.append(ChainStep(
            lhs=joined(expressions[position]),
            rhs=joined(expressions[position + 1]),
            relation=relation,
            reversed=reverse,
            justification=joined(justification) if justification else "",
            span=span,
        ))

    return steps


def is_pi_type(goal: str) -> bool:
    depth = 0

    for char in goal:
        if char in "({[":
            depth += 1
        elif char in ")}]":
            depth -= 1
        elif char == "→" and depth == 0:
            return True

    return goal.lstrip().startswith("∀")


def get_signature_line(source: str, target_name: str) -> str:
    """
    Return target_name's signature on one line, with its continuation lines
    (a signature may span several) joined.

    Example:
        plusZero : (n : Nat) → n + 0 ≡ n
    """

    prefix = f"{target_name} :"
    lines = source.splitlines()

    for index, line in enumerate(lines):
        stripped = line.strip()

        if not stripped.startswith(prefix):
            continue

        column = len(line) - len(line.lstrip())
        parts = [stripped]

        for follow in lines[index + 1:]:
            if follow.strip() and len(follow) - len(follow.lstrip()) > column:
                parts.append(follow.strip())
            else:
                break

        return " ".join(parts)

    raise ValueError(f"Could not find signature line for {target_name}.")
