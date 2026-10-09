"""
Placing holes in a proof attempt that does not check.

A model's formal proof attempt usually fails somewhere specific: a wrong
lemma name, a misordered argument, an unjustified step. Rather than throwing
the attempt away, `place_holes` keeps as much of it as Agda accepts and puts
holes where it went wrong:

    1. a `begin ... ∎` chain keeps its stated steps; its justifications
       become holes;
    2. then, repeatedly, the smallest piece around Agda's error that changes
       the error becomes a hole: the enclosing parenthesised group, then the
       pair component, then the clause's whole right-hand side.

The result is the attempt's own decomposition, with holes where it was wrong:
a sketch, in DSP's sense, made from the attempt rather than asked for.

Also here: `sketch_clauses` and `split_declaration`, which take a model's
declaration text apart into signature and clauses, and `model_names`, the
lemma-like names an attempt used (good Mimer hints).
"""

from __future__ import annotations

import re
from pathlib import Path

from core.agda_client import check_sketch
from core.hammer import HammerConfig
from util.agda_source import WORD_RE, declaration_span, parse_clauses
from util.sketch_ops import mask_comments


def place_holes(
    agda_file: Path,
    trial: str,
    check,
    name: str,
    signature_line: int | None,
    hammer: HammerConfig,
    repairs: list[str],
):
    """
    Place holes in the failing declaration `name` in `trial`, as the module
    docstring describes. Returns the new text and its check (still an error
    if nothing helped); each change is appended to `repairs`. The file holds
    the returned text.
    """

    if check.kind == "error":
        start, body_start, end, _ = declaration_span(trial, name, signature_line)
        body = trial[body_start:end]
        holed = hole_chain_justifications(body)

        if holed != body:
            trial = trial[:body_start] + holed + trial[end:]
            agda_file.write_text(trial)
            # keep the holed chain even if something else still fails: the
            # next repair works on whatever error remains
            check = recheck(agda_file, hammer)
            repairs.append("chain justifications → holes")

    for _ in range(10):
        if check.kind != "error":
            break

        target = _clause_at_error(check.message, trial, name, signature_line)
        error_span = _error_span(check.message, trial)

        if target is None or error_span is None:
            break

        lhs, rhs_span = target
        before = _error_text(check.message)
        fixed = False

        for start, stop in _enclosing_spans(trial, error_span, rhs_span):
            attempt = trial[:start] + "{!!}" + trial[stop:]
            agda_file.write_text(attempt)
            result = recheck(agda_file, hammer)

            if result.kind != "error" or _error_text(result.message) != before:
                whole = (start, stop) == rhs_span
                piece = " ".join(trial[start:stop].split())
                repairs.append(
                    f"clause `{lhs}` → hole" if whole else f"`{piece[:60]}` in `{lhs}` → hole"
                )
                trial, check, fixed = attempt, result, True
                break

        if not fixed:
            break

    agda_file.write_text(trial)

    return trial, check


def recheck(agda_file: Path, hammer: HammerConfig):
    return check_sketch(
        agda_file, import_path=hammer.import_path, with_context=True, timeout=hammer.agda_timeout,
    )


def _clause_at_error(
    message: str, trial: str, name: str, signature_line: int | None
) -> tuple[str, tuple[int, int]] | None:
    """
    The clause of `name` whose right-hand side holds the position Agda's
    error points at (or whose where block does), and that right-hand side's
    span. None when the error is elsewhere: in a clause's left-hand side, say.
    """

    where = re.search(r":(\d+)[.,](\d+)", message)

    if where is None:
        return None

    lines = trial.splitlines(keepends=True)
    row, col = int(where.group(1)), int(where.group(2))

    if not 0 < row <= len(lines):
        return None

    offset = sum(len(l) for l in lines[: row - 1]) + col - 1

    try:
        _, clauses = parse_clauses(trial, name, signature_line)
    except ValueError:
        return None

    spans = [(c.lhs, c.rhs_span) for c in clauses if c.rhs_span is not None]

    for index, (lhs, (start, stop)) in enumerate(spans):
        # a clause's where block runs on until the next clause starts
        block_end = spans[index + 1][1][0] if index + 1 < len(spans) else len(trial)
        if start <= offset < block_end and trial[start:stop].strip() != "{!!}":
            # the where block, if any, goes with the right-hand side
            stop_with_where = _where_end(trial, stop, block_end)
            return lhs, (start, stop_with_where if offset >= stop else stop)

    return None


def _error_span(message: str, trial: str) -> tuple[int, int] | None:
    """Offsets of the range Agda's first error gives (`L.C-C` or `L.C-L.C`)."""

    where = re.search(r":(\d+)[.,](\d+)(?:-(?:(\d+)[.,])?(\d+))?", message)

    if where is None:
        return None

    lines = trial.splitlines(keepends=True)
    starts = [0]
    for line in lines:
        starts.append(starts[-1] + len(line))

    def offset(row: int, col: int) -> int | None:
        return starts[row - 1] + col - 1 if 0 < row <= len(lines) else None

    first_row, first_col = int(where.group(1)), int(where.group(2))
    last_row = int(where.group(3)) if where.group(3) else first_row
    last_col = int(where.group(4)) if where.group(4) else first_col + 1
    start, stop = offset(first_row, first_col), offset(last_row, last_col)

    return (start, stop) if start is not None and stop is not None else None


def _error_text(message: str) -> str:
    """An error without its positions, to tell whether a hole changed it."""

    return re.sub(r"\S*:\d+[.,]\d+(?:-(?:\d+[.,])?\d+)?", "", message).strip()[:300]


def _enclosing_spans(
    trial: str, error: tuple[int, int], rhs: tuple[int, int]
) -> list[tuple[int, int]]:
    """
    Candidate spans to hole, smallest first: the parenthesised groups inside
    the right-hand side that contain the error, then the top-level pair
    component (`a , b`) holding it, then the whole right-hand side.
    """

    rhs_start, rhs_stop = rhs
    text = mask_comments(trial)[rhs_start:rhs_stop]
    error_start, error_stop = error[0] - rhs_start, error[1] - rhs_start
    groups: list[tuple[int, int]] = []
    stack: list[int] = []
    commas: list[int] = []

    for index, char in enumerate(text):
        if char == "(":
            stack.append(index)
        elif char == ")" and stack:
            open_at = stack.pop()
            if open_at <= error_start and index + 1 >= error_stop:
                groups.append((open_at, index + 1))
        elif char == "," and not stack and text[index - 1:index + 2] == " , ":
            commas.append(index)

    spans = sorted(groups, key=lambda g: g[1] - g[0])

    if commas:
        bounds = [0] + [c + 1 for c in commas] + [len(text)]
        for lo, hi in zip(bounds, bounds[1:]):
            piece = text[lo:hi].rstrip(" ,")
            lead = len(piece) - len(piece.lstrip())
            if lo <= error_start < hi:
                spans.append((lo + lead, lo + len(piece)))

    out = [(rhs_start + a, rhs_start + b) for a, b in spans if (a, b) != (0, len(text))]

    return list(dict.fromkeys(out)) + [rhs]


def _where_end(trial: str, rhs_end: int, limit: int) -> int:
    """End of a `where` block right after a right-hand side, or rhs_end."""

    rest = trial[rhs_end:limit]
    match = re.match(r"\s*\n(\s+)where\b", rest)

    if not match:
        return rhs_end

    # through the last indented line before the next clause
    body = rest.rstrip()
    return rhs_end + len(body)


def model_names(completion: str, name: str) -> list[str]:
    """Names the model used that look like lemmas, as Mimer hints (at most 12)."""

    words = []
    for word in WORD_RE.findall(completion):
        word = word.strip(".,;")
        if (
            word != name and len(word) > 2 and not word.startswith(("{", "--"))
            and re.search(r"[-ʳˡ′⁺⁻₀₁₂]|[a-z][A-Z]", word) and word not in words
        ):
            words.append(word)

    return words[:12]


_JUSTIFICATION_RE = re.compile(r"(\S+?˘?⟨)(?!⟩)(.*?)(\s[⟩⟨](?=\s|$))", re.DOTALL)


def hole_chain_justifications(clauses: str) -> str:
    """Every `R⟨ p ⟩` in the clauses' chains becomes `R⟨ {!!} ⟩`; `R⟨⟩` stays."""

    if not re.search(r"\bbegin", clauses):
        return clauses

    return _JUSTIFICATION_RE.sub(lambda m: f"{m.group(1)} {{!!}}{m.group(3)}", clauses)


def sketch_clauses(text: str, name: str) -> str:
    """
    The clauses of `name` from a model's sketch, without its signature,
    dedented. Comments directly above a clause stay with it; anything that is
    not a clause of `name` (a lemma proved inline, prose) is dropped.
    """

    lines = text.splitlines()
    kept: list[str] = []
    pending: list[str] = []
    keeping = False
    signature = re.compile(rf"^\s*{re.escape(name)}\s*:(?!:)")
    in_signature = False

    for line in lines:
        stripped = line.strip()

        if not stripped:
            if keeping:
                kept.append("")
            continue

        if stripped.startswith("--"):
            (kept if keeping and line[:1].isspace() else pending).append(line)
            continue

        if signature.match(line):
            in_signature, keeping, pending = True, False, []
            continue

        head = re.split(r"[\s(){}]", stripped, maxsplit=1)[0]

        if head == name or stripped.startswith("..."):
            in_signature, keeping = False, True
            kept.extend(pending)
            pending = []
            kept.append(line)
            continue

        if line[:1].isspace() and keeping:
            kept.append(line)
            continue

        if line[:1].isspace() and in_signature:
            continue

        keeping, in_signature, pending = False, False, []

    while kept and not kept[-1].strip():
        kept.pop()

    indent = min((len(l) - len(l.lstrip()) for l in kept if l.strip()), default=0)

    return "\n".join(l[indent:] for l in kept)


def split_declaration(text: str, name: str) -> tuple[str, str]:
    """(type of `name`, its clauses) from a model's declaration text."""

    lines = text.strip("\n").splitlines()
    signature: list[str] = []
    rest = len(lines)

    for index, line in enumerate(lines):
        if index == 0:
            match = re.match(rf"^\s*{re.escape(name)}\s*:(?!:)(.*)$", line)
            if not match:
                return "", ""
            signature.append(match.group(1))
            continue
        if line[:1].isspace() or not line.strip():
            signature.append(line)
            continue
        rest = index
        break

    return " ".join(" ".join(signature).split()), sketch_clauses("\n".join(lines[rest:]), name)
