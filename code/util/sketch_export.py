"""
Turning a finished proof back into a sketch: the analytic way of placing
holes, from a proof that is known to be right.

`export_sketch` writes the same file with holes where the proof's work was,
at clause, step or lemma granularity (see `Sketch`), and checks with Agda
that the holes are well placed and that putting the original justifications
back typechecks. The decomposition it works from comes from util.deproof.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

from core.agda_client import check_sketch
from core.proof_files import preserved_file
from util.agda_source import (
    META_RE,
    QUALIFIED_RE,
    WORD_RE,
    Clause,
    parse_clauses,
    indentation,
    is_pi_type,
    signature_index,
)
from util.deproof import (
    DEFAULT_CONGRUENCES,
    DEPROOF_TIMEOUT_SECONDS,
    ClauseDecomposition,
    Decomposition,
    ProofStep,
    decompose,
)
from util.sketch_ops import count_holes


GRANULARITIES = ("clause", "step", "lemma")


@dataclass
class Sketch:
    """
    A finished proof turned back into a sketch: the same file with holes
    where the proof's work was, at one granularity.

        clause   each clause's right-hand side is one hole
        step     each step of a clause is a local `where` declaration with
                 its statement written out and a hole for its proof, and the
                 clause chains them with `trans` (steps that hold by `refl`
                 stay inline)
        lemma    as `step`, but steps that do not use the induction
                 hypothesis become top-level lemmas, quantified over the
                 variables they mention

    `filled` is the same skeleton with the original justifications in place
    of the holes; it typechecking is what shows the sketch is faithful to the
    proof. `problems` is empty when both checks passed. `warnings` flag holes
    that check but are not well placed: a goal with unsolved metas (not
    determined by the sketch alone) or of function type (the clause binds
    fewer arguments than the type takes, as point-free proofs do).
    """

    name: str
    granularity: str
    source: str
    filled: str
    excerpt: str = ""     # just the rewritten declaration and the lemmas added for it
    holes: list[str] = field(default_factory=list)     # goal of each new hole
    lemmas: list[str] = field(default_factory=list)    # top-level lemmas introduced
    problems: list[str] = field(default_factory=list)  # it does not check: invalid
    warnings: list[str] = field(default_factory=list)  # it checks, but a hole is badly placed
    notes: list[str] = field(default_factory=list)     # where it is coarser than the decomposition

    @property
    def valid(self) -> bool:
        return not self.problems


def export_sketch(
    agda_file: Path,
    name: str,
    granularity: str = "step",
    import_path: str | None = None,
    decomposition: Decomposition | None = None,
    annotate: bool = False,
    congruences: tuple[str, ...] = DEFAULT_CONGRUENCES,
    line: int | None = None,
    timeout: int = DEPROOF_TIMEOUT_SECONDS,
) -> Sketch:
    """
    Turn the finished declaration `name` in `agda_file` into a sketch and
    check it with Agda. The file is restored afterwards. With `annotate`,
    each hole is preceded by a comment giving the justification it replaced.
    `line` picks the declaration when its name occurs more than once.
    """

    if granularity not in GRANULARITIES:
        raise ValueError(f"granularity must be one of {GRANULARITIES}, not {granularity!r}")

    source = agda_file.read_text()
    decomposition = decomposition or decompose(
        agda_file, name, import_path=import_path, congruences=congruences,
        line=line, timeout=timeout,
    )
    _, clauses = parse_clauses(source, name, line)
    lines = source.splitlines()
    column = indentation(lines[signature_index(lines, name, line)])

    if len(clauses) != len(decomposition.clauses):
        raise ValueError("The decomposition does not match the file's clauses.")

    exclude: set[tuple[int, int]] = set()
    notes: list[str] = []

    # At lemma granularity a lifted lemma can still fail to check for reasons
    # the text does not show (an irrelevant or instance argument it does not
    # carry). Then the lemma Agda points at goes back to being a hole and the
    # sketch is rebuilt, a few times at most.
    for _ in range(MAX_DEMOTIONS + 1):
        sketch, keys = _build_sketch(
            source, name, granularity, decomposition, clauses, column, line,
            annotate, frozenset(exclude),
        )
        _validate(agda_file, sketch, source, import_path, timeout)

        if sketch.valid or granularity != "lemma":
            break

        blamed = _blamed_lemma(sketch)

        if blamed is None and keys:
            # Some errors carry no position (unsolved constraints at the end
            # of the file). The usual culprit is a lemma whose implicit
            # arguments the call cannot determine, so demote the last such
            # lemma, or else the last lemma.
            implicit = [n for n in keys if re.search(rf"^\s*{re.escape(n)} : .*{{", sketch.source, re.M)]
            blamed = (implicit or list(keys))[-1]

        if blamed is None or blamed not in keys:
            break

        exclude.add(keys[blamed])
        notes.append(f"{blamed} did not check as a lemma; that step stays a hole")

    sketch.notes = sketch.notes + notes

    return sketch


MAX_DEMOTIONS = 4


def _build_sketch(
    source: str,
    name: str,
    granularity: str,
    decomposition: Decomposition,
    clauses: list[Clause],
    column: int,
    line: int | None,
    annotate: bool,
    exclude: frozenset[tuple[int, int]],
) -> tuple[Sketch, dict[str, tuple[int, int]]]:
    """The sketch, unvalidated, and the (clause, step) key of each lifted lemma."""

    fresh = _fresh_names(set(WORD_RE.findall(source)))
    holed, filled = source, source
    holes: list[str] = []
    lemmas_holed: list[str] = []
    lemmas_filled: list[str] = []
    keys: dict[str, tuple[int, int]] = {}
    problems: list[str] = []

    # Build in source order (so fresh names count up), then splice back to
    # front so earlier spans stay valid.
    rewrites = []

    for clause_index, (clause, entry) in enumerate(zip(clauses, decomposition.clauses)):
        if clause.rhs_span is None:
            continue

        rewrite = _clause_rewrite(
            entry, clause, granularity, name, fresh, annotate,
            only_clause=len(decomposition.clauses) == 1,
            source=source, column=column,
            clause_index=clause_index, exclude=exclude,
        )

        if rewrite is not None:
            rewrites.append((clause.rhs_span, entry, rewrite))

    notes: list[str] = []

    for (start, end), entry, rewrite in reversed(rewrites):
        (rhs_holed, rhs_filled), new_lemmas, new_holes, problem, note = rewrite

        if problem:
            problems.insert(0, f"clause {entry.lhs}: {problem}")

        if note:
            notes.insert(0, note)

        holed = holed[:start] + rhs_holed + holed[end:]
        filled = filled[:start] + rhs_filled + filled[end:]
        holes[:0] = new_holes
        lemmas_holed[:0] = [h for h, _, _ in new_lemmas]
        lemmas_filled[:0] = [f for _, f, _ in new_lemmas]

        for text, _, key in new_lemmas:
            keys[text.split(" :", 1)[0]] = key

    lemma_names = [text.split(" :", 1)[0] for text in lemmas_holed]
    excerpt = _declaration_excerpt(holed, name, line, column, lemmas_holed)

    if lemmas_holed:
        holed = _insert_before_declaration(holed, name, lemmas_holed, line, column)
        filled = _insert_before_declaration(filled, name, lemmas_filled, line, column)

    sketch = Sketch(
        name=name, granularity=granularity, source=holed, filled=filled,
        excerpt=excerpt, lemmas=lemma_names, problems=problems, notes=notes,
    )

    return sketch, keys


def _blamed_lemma(sketch: Sketch) -> str | None:
    """The lifted lemma named on the line Agda's first error points at."""

    for problem in sketch.problems:
        text = sketch.filled if problem.startswith("filled") else sketch.source
        where = re.search(r":(\d+)[.,]\d+", problem)

        if where is None:
            continue

        lines = text.splitlines()
        number = int(where.group(1))

        if not 0 < number <= len(lines):
            continue

        words = set(WORD_RE.findall(lines[number - 1]))

        for lemma in sketch.lemmas:
            if lemma in words:
                return lemma

    return None


def _fresh_names(taken: set[str]):
    counters: dict[str, int] = {}

    def fresh(base: str) -> str:
        while True:
            counters[base] = counters.get(base, 0) + 1
            candidate = f"{base}{counters[base]}"
            if candidate not in taken:
                taken.add(candidate)
                return candidate

    return fresh


def _clause_rewrite(
    entry: ClauseDecomposition,
    clause: Clause,
    granularity: str,
    name: str,
    fresh,
    annotate: bool,
    only_clause: bool = False,
    source: str = "",
    column: int = 0,
    clause_index: int = 0,
    exclude: frozenset[tuple[int, int]] = frozenset(),
):
    """
    ((holed rhs, filled rhs), [(holed lemma, filled lemma, key)], [hole
    goals], problem, note) for one clause, or None to leave the clause alone.
    A key is (clause, step); steps whose key is in `exclude` are not lifted.
    A note says where the sketch had to be coarser than the decomposition.
    """

    pad = " " * column
    steps = entry.steps

    def comment(step: ProofStep, indent: str) -> str:
        return f"{indent}-- was: {step.justification}\n" if annotate else ""

    # A single step is the clause itself. It becomes a lemma only if that
    # says something new: not when it uses the induction hypothesis, and not
    # when the clause is the whole declaration (the lemma would restate it).
    single = clause.chain is None and len(steps) <= 1 and (
        granularity == "step" or only_clause or any(s.recursive for s in steps)
    )

    if granularity == "clause" or single:
        prefix = f"-- was: {clause.rhs}\n{pad}  " if annotate else ""
        return (f"{prefix}{{!!}}", clause.rhs), [], [entry.goal], "", ""

    if clause.chain is not None:
        return _chain_rewrite(
            entry, clause, granularity, name, fresh, source, clause_index, exclude
        )

    if clause.note:
        # An existing where block cannot take a second one; leave it whole.
        return None

    # Chained steps must be equations (they are joined with `trans`), and a
    # step that is not lifted is written out as a `where` step, so its
    # statement must be writable there. When that fails the clause stays one
    # hole: the decomposition is still recorded, the sketch is just coarser.
    def lifted(position: int, step: ProofStep) -> bool:
        return (
            granularity == "lemma" and (clause_index, position) not in exclude
            and _liftable(step, step.statement, clause, entry)
        )

    unwritable = [
        s for position, s in enumerate(steps)
        if not (s.justification == "refl" and len(steps) > 1)
        and (not s.sides or not (lifted(position, s) or _writable(s.statement, entry)))
    ]

    if unwritable:
        return (
            ("{!!}", clause.rhs), [], [entry.goal],
            "",
            f"clause {entry.lhs}: kept as one hole, since an intermediate statement "
            "cannot be written in this file's scope",
        )

    where_holed: list[str] = []
    where_filled: list[str] = []
    lemmas: list[tuple[str, str]] = []
    holes: list[str] = []
    calls: list[str] = []
    inner = pad + "    "

    for position, step in enumerate(steps):
        # A step that holds by computation is not a piece of the decomposition.
        if step.justification == "refl" and len(steps) > 1:
            calls.append("refl")
            continue

        key = (clause_index, position)

        if granularity == "lemma" and key not in exclude and _liftable(step, step.statement, clause, entry):
            lemma, call = _lift(entry, step.statement, step, name, fresh)
            lemmas.append((
                f"{lemma}\n{comment(step, '')}{call} = {{!!}}\n",
                f"{lemma}\n{call} = {step.justification}\n",
                key,
            ))
            holes.append(step.statement)
            calls.append(call)
            continue

        local = fresh("step")
        where_holed.append(
            f"{inner}{local} : {step.statement}\n{comment(step, inner)}{inner}{local} = {{!!}}"
        )
        where_filled.append(
            f"{inner}{local} : {step.statement}\n{inner}{local} = {step.justification}"
        )
        holes.append(step.statement)
        calls.append(local)

    def atom(term: str) -> str:
        return f"({term})" if " " in term else term

    body = calls[-1]

    for call in reversed(calls[:-1]):
        body = f"trans {atom(call)} {atom(body)}"

    def with_where(where_lines: list[str]) -> str:
        return body + (f"\n{pad}  where\n" + "\n".join(where_lines) if where_lines else "")

    return (with_where(where_holed), with_where(where_filled)), lemmas, holes, "", ""


def _chain_rewrite(
    entry: ClauseDecomposition,
    clause: Clause,
    granularity: str,
    name: str,
    fresh,
    source: str,
    clause_index: int,
    exclude: frozenset[tuple[int, int]],
):
    """
    A `begin ... ∎` chain already states every intermediate expression, so it
    stays as written and only the justifications change: each becomes a hole
    (step), or a call to a new top-level lemma whose proof is the hole
    (lemma). `REL⟨⟩` steps hold by computation and stay. At lemma
    granularity only `≡` steps that do not use the induction hypothesis are
    lifted; any other relation's statement depends on its setoid or order,
    so those steps stay holes.
    """

    assert clause.rhs_span is not None and clause.chain is not None

    start, end = clause.rhs_span
    rhs = source[start:end]
    holed_parts: list[tuple[int, int, str]] = []
    filled_parts: list[tuple[int, int, str]] = []
    lemmas: list[tuple[str, str]] = []
    holes: list[str] = []

    for position, (link, step) in enumerate(zip(clause.chain, entry.steps)):
        if link.span is None:
            continue

        offset = (link.span[0] - start, link.span[1] - start)
        # What the justification proves: a reversed step proves rhs ~ lhs.
        proves = f"{link.rhs} {link.relation} {link.lhs}" if link.reversed else step.statement
        key = (clause_index, position)

        if (
            granularity == "lemma" and link.relation == "≡" and key not in exclude
            and _liftable(step, proves, clause, entry)
        ):
            lemma, call = _lift(entry, proves, step, name, fresh)
            lemmas.append((
                f"{lemma}\n{call} = {{!!}}\n", f"{lemma}\n{call} = {link.justification}\n", key,
            ))
            holed_parts.append((*offset, call))
            filled_parts.append((*offset, call))
        else:
            holed_parts.append((*offset, "{!!}"))

        holes.append(proves)

    def spliced(parts: list[tuple[int, int, str]]) -> str:
        text = rhs
        for a, b, replacement in sorted(parts, reverse=True):
            text = text[:a] + replacement + text[b:]
        return text

    return (spliced(holed_parts), spliced(filled_parts)), lemmas, holes, "", ""




def _liftable(
    step: ProofStep, statement: str, clause: Clause, entry: ClauseDecomposition
) -> bool:
    """
    Whether a step can become a top-level lemma at all: not if it uses the
    induction hypothesis, not if it mentions something declared in the
    clause's own `where` block (out of scope at top level), and not if Agda
    printed its statement or a binder's type with qualified names
    (`Data.Empty.⊥`), which name things the file has not brought into scope.
    """

    words = set(WORD_RE.findall(statement)) | set(WORD_RE.findall(step.justification))
    binders, _ = _quantify(entry, statement, step)

    return not (
        step.recursive
        or words & clause.local_names
        or QUALIFIED_RE.search(statement)
        or QUALIFIED_RE.search(binders)
    )


def _writable(statement: str, entry: ClauseDecomposition) -> bool:
    """
    Whether a statement can be written inside the clause (as a `where`
    step): it must be known, fully determined, use no qualified names, and
    mention no variable the clause leaves unnamed.
    """

    return bool(statement) and not (
        META_RE.search(statement)
        or QUALIFIED_RE.search(statement)
        or set(WORD_RE.findall(statement)) & set(entry.hidden)
    )


def _lift(
    entry: ClauseDecomposition, statement: str, step: ProofStep, name: str, fresh
) -> tuple[str, str]:
    """A top-level lemma for one step: (signature, call with its arguments)."""

    lemma = fresh(f"{name}-lemma")
    binders, arguments = _quantify(entry, statement, step)
    call = f"{lemma} {' '.join(arguments)}".strip()

    return f"{lemma} : {binders}{statement}", call


def _quantify(
    entry: ClauseDecomposition, statement: str, step: ProofStep
) -> tuple[str, list[str]]:
    """
    Binders and call arguments for lifting a step to a top-level lemma: the
    clause's variables its statement or proof mentions, plus those their
    types depend on, in binding order. A variable the clause never names (an
    implicit argument it does not bind) becomes an implicit binder for Agda
    to infer at the call; the rest are explicit and passed. Module
    parameters are left alone: the lemma sits in the same module.
    """

    words = set(WORD_RE.findall(statement)) | set(WORD_RE.findall(step.justification))
    # Module parameters are in scope where the lemma goes; only what the
    # clause binds (or leaves implicit) needs quantifying.
    context = [v for v in entry.variable_types if v in entry.variables or v in entry.hidden]
    needed = {v for v in context if v in words}

    while True:
        more = {
            v for v in context
            if v not in needed
            and any(v in WORD_RE.findall(entry.variable_types[n]) for n in needed)
        }
        if not more:
            break
        needed |= more

    order = [v for v in context if v in needed]
    binders = "".join(
        f"{{{v} : {entry.variable_types[v]}}} → " if v in entry.hidden
        else f"({v} : {entry.variable_types[v]}) → "
        for v in order
    )

    return binders, [v for v in order if v not in entry.hidden]


def _declaration_excerpt(
    source: str, name: str, line: int | None, column: int, lemmas: list[str]
) -> str:
    """The declaration's lines in `source`, preceded by the lemmas to be added."""

    lines = source.splitlines()
    start = signature_index(lines, name, line)
    end = start + 1

    while end < len(lines):
        text = lines[end]
        head = re.split(r"[\s(){}]", text.strip(), maxsplit=1)[0]
        if text.strip() and indentation(text) <= column and head != name:
            break
        end += 1

    pad = " " * column
    added = [
        "\n".join(pad + t if t.strip() else t for t in lemma.rstrip("\n").split("\n"))
        for lemma in lemmas
    ]

    return "\n".join(added + ["\n".join(lines[start:end]).rstrip()])


def _insert_before_declaration(
    source: str, name: str, declarations: list[str], line: int | None, column: int
) -> str:
    lines = source.splitlines(keepends=True)
    index = signature_index(lines, name, line)

    # Keep a comment block that documents the declaration attached to it.
    while index > 0 and lines[index - 1].lstrip().startswith("--"):
        index -= 1

    pad = " " * column
    block = "".join(
        "\n".join(pad + text if text.strip() else text for text in decl.split("\n")) + "\n"
        for decl in declarations
    )

    return "".join(lines[:index]) + block + "".join(lines[index:])


def _validate(
    agda_file: Path,
    sketch: Sketch,
    original: str,
    import_path: str,
    timeout: int = DEPROOF_TIMEOUT_SECONDS,
) -> None:
    """
    The holed file must load with every new hole's goal fully determined (no
    metas) and not a function type; the filled file must check with no more
    holes than the original had.
    """

    baseline = count_holes(original)

    with preserved_file(agda_file):
        agda_file.write_text(sketch.source)
        holed = check_sketch(agda_file, import_path=import_path, with_context=False, timeout=timeout)

        if holed.kind == "error":
            sketch.problems.append(f"sketch does not typecheck: {holed.message[:500]}")
        else:
            goals = [goal.type for goal in holed.goals]
            sketch.holes = goals

            if len(goals) - baseline != count_holes(sketch.source) - baseline:
                sketch.problems.append(
                    f"Agda reports {len(goals)} goals for {count_holes(sketch.source)} holes"
                )

            for goal in goals:
                if META_RE.search(goal):
                    sketch.warnings.append(f"hole goal not determined: {goal}")
                elif is_pi_type(goal):
                    sketch.warnings.append(f"hole goal is a function type: {goal}")

        agda_file.write_text(sketch.filled)
        filled = check_sketch(agda_file, import_path=import_path, with_context=False, timeout=timeout)

        if filled.kind == "error":
            sketch.problems.append(f"filled sketch does not typecheck: {filled.message[:500]}")
        elif len(filled.goals) != baseline:
            sketch.problems.append(
                f"filled sketch has {len(filled.goals)} holes, the original {baseline}"
            )
