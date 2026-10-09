"""
Take a finished Agda proof apart into the decomposition it implies.

Given a declaration that typechecks, `decompose` reports:

    * its case split (one entry per clause, with the clause's goal);
    * the steps of each clause: the `trans` structure of the right-hand side
      is flattened into a chain (pushing `sym` and congruences inside), and
      Agda infers each step's statement at the clause's hole;
    * which lemmas each step uses, which steps use the induction hypothesis
      (a recursive call), and the type of every lemma used.

    addComm (suc n) m = trans (congSuc (addComm n m)) (sym (plusSucLeft m n))

      clause addComm (suc n) m      goal: suc n + m ≡ m + suc n
        1. suc (n + m) ≡ suc (m + n)    by congSuc (addComm n m)   [IH, congSuc]
        2. suc (m + n) ≡ m + suc n      by sym (plusSucLeft m n)   [plusSucLeft]

Each step is a hole a sketch could have left, and each lemma is a piece the
proof was decomposed into. `Decomposition.render()` is the text form, meant to
be shown to a model; `compare` lines up two decompositions of the same
theorem (a reference and a candidate, or two candidates).

util/sketch_export.py goes the other way, turning the finished proof back
into a typecheckable sketch with holes; util/agda_source.py does the reading
of declarations, clauses and chains that both rely on.

Run from code/:

    python util/deproof.py FILE NAME [--compare OTHER_FILE]
    python util/deproof.py FILE NAME --sketch {clause,step,lemma} [--annotate] [--out PATH]

Limits: `with` headers and the bodies of `where` blocks are not taken apart
(a `with`'s continuation clauses are), and only `trans`, `sym` and the given
congruence names are seen through.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass, field
from pathlib import Path

from core import config
from core.agda_client import AgdaSession
from core.config import AGDA_IMPORT_PATH
from core.proof_files import preserved_file
from util.checkout import mirrored
from util.agda_source import (
    META_RE,
    WORD_RE,
    ChainStep,
    Clause,
    parse_clauses,
    split_equation,
)
from util.sketch_ops import find_holes


# A term is an atom or an application spine [head, arg, ...].
Term = str | list


DEFAULT_CONGRUENCES: tuple[str, ...] = ("cong",)

# Loading a library module (with its holes) in interaction mode, cold, can
# take minutes; the pipeline's 30 s default is for the small test files.
DEPROOF_TIMEOUT_SECONDS = 600
STRUCTURAL = frozenset({"trans", "sym"})



# ---------------------------------------------------------------------------
# Results
# ---------------------------------------------------------------------------


@dataclass
class ProofStep:
    """
    One step of a clause: `statement`, closed by `justification`.

    A step of a `begin ... ∎` chain is read off the source: its sides are the
    expressions the author wrote, `relation` is the chain's (`≡`, `≈`, `≤`,
    ...), `reversed` marks a `≡˘⟨ p ⟩` / `≡⟨ p ⟨` step (p proves rhs ~ lhs),
    and an empty justification is a `≡⟨⟩` step, which holds by computation.
    A step taken from a `trans` term has its statement inferred by Agda.
    """

    statement: str        # as written in a chain, else as Agda displays it
    justification: str
    head: str             # the name doing the work once sym/cong are peeled off
    uses: list[str] = field(default_factory=list)  # lemma names, IH excluded
    recursive: bool = False                         # uses the induction hypothesis
    normal: str = ""      # fully normalised statement, for comparisons
    lhs: str = ""
    rhs: str = ""
    relation: str = "≡"
    reversed: bool = False

    @property
    def sides(self) -> tuple[str, str] | None:
        if self.lhs and self.rhs:
            return self.lhs, self.rhs

        try:
            return split_equation(self.statement)
        except ValueError:
            return None


@dataclass
class ClauseDecomposition:
    lhs: str
    goal: str = ""
    variables: list[str] = field(default_factory=list)  # pattern variables, in order
    # Everything in Agda's context at the clause's hole, in binding order,
    # including variables the clause never names (`hidden`: implicit
    # arguments it does not bind, which Agda shows but which are not in scope).
    variable_types: dict[str, str] = field(default_factory=dict)
    hidden: list[str] = field(default_factory=list)
    steps: list[ProofStep] = field(default_factory=list)
    note: str = ""        # why a clause was not (fully) taken apart

    def midpoints(self, normal: bool = False) -> list[str]:
        """Intermediate expressions of an equational chain, endpoints excluded."""

        sides: list[tuple[str, str] | None] = []

        for step in self.steps:
            if normal and step.normal:
                try:
                    sides.append(split_equation(step.normal))
                except ValueError:
                    sides.append(None)
            else:
                sides.append(step.sides)

        known = [side for side in sides if side is not None]

        if len(known) < 2 or len(known) != len(sides):
            return []

        return [rhs for _, rhs in known[:-1] if not META_RE.search(rhs)]


@dataclass
class Decomposition:
    name: str
    signature: str
    clauses: list[ClauseDecomposition] = field(default_factory=list)
    lemmas: dict[str, str] = field(default_factory=dict)        # name -> type as declared
    lemma_normal: dict[str, str] = field(default_factory=dict)  # name -> normalised type

    @property
    def n_steps(self) -> int:
        return sum(len(clause.steps) for clause in self.clauses)

    @classmethod
    def from_dict(cls, data: dict) -> Decomposition:
        """Rebuild one from its logged (dataclasses.asdict) form."""

        clauses = [
            ClauseDecomposition(**{
                **clause, "steps": [ProofStep(**step) for step in clause.get("steps", [])],
            })
            for clause in data.get("clauses", [])
        ]

        return cls(**{**data, "clauses": clauses})

    def render(self) -> str:
        lines = [
            self.signature,
            f"{len(self.clauses)} clause(s), {self.n_steps} step(s), "
            f"lemmas: {', '.join(self.lemmas) or '(none)'}",
        ]

        for clause in self.clauses:
            lines.append("")
            lines.append(f"clause {clause.lhs}")
            if clause.goal:
                lines.append(f"  goal: {clause.goal}")
            if clause.note:
                lines.append(f"  ({clause.note})")

            for index, step in enumerate(clause.steps, start=1):
                tags = (["IH"] if step.recursive else []) + step.uses
                tag_text = f"   [{', '.join(tags)}]" if tags else ""
                how = step.justification or "computation"
                if step.reversed:
                    how += "  (reversed)"
                lines.append(f"  {index}. {step.statement}")
                lines.append(f"       by {how}{tag_text}")

        if self.lemmas:
            lines.append("")
            lines.append("lemmas used:")
            lines.extend(f"  {name} : {type_}" for name, type_ in self.lemmas.items())

        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Terms
# ---------------------------------------------------------------------------


def parse_term(text: str) -> Term:
    """Parse into application spines. `{...}` implicit arguments stay atomic."""

    tokens: list[str] = []
    i = 0

    while i < len(text):
        char = text[i]

        if char.isspace():
            i += 1
        elif char in "()":
            tokens.append(char)
            i += 1
        elif text.startswith("{!", i):
            # A hole is an explicit argument, whatever is written inside it.
            j = text.find("!}", i)
            j = len(text) if j == -1 else j + 2
            tokens.append(text[i:j])
            i = j
        elif char == "{":
            depth, j = 0, i
            while j < len(text):
                depth += text[j] == "{"
                depth -= text[j] == "}"
                j += 1
                if depth == 0:
                    break
            tokens.append(text[i:j])
            i = j
        else:
            j = i
            while j < len(text) and not text[j].isspace() and text[j] not in "(){":
                j += 1
            tokens.append(text[i:j])
            i = j

    position = 0

    def sequence(stop: str | None) -> Term:
        nonlocal position
        items: list[Term] = []

        while position < len(tokens) and tokens[position] != stop:
            if tokens[position] == "(":
                position += 1
                items.append(sequence(")"))
                position += 1
            elif tokens[position] == ")":   # unbalanced: skip it
                position += 1
            else:
                items.append(tokens[position])
                position += 1

        if not items:
            if stop is not None:            # `()`: the unit value or an absurd pattern
                return "()"
            raise ValueError(f"Empty term in {text!r}.")

        return items[0] if len(items) == 1 else items

    return sequence(None)


def show_term(term: Term) -> str:
    if isinstance(term, str):
        return term

    return " ".join(
        part if isinstance(part, str) else f"({show_term(part)})" for part in term
    )


def flatten_steps(
    term: Term, congruences: tuple[str, ...] = DEFAULT_CONGRUENCES
) -> list[Term]:
    """
    trans p q    -> steps(p) ++ steps(q)
    sym p        -> reversed sym-steps(p), when p has more than one step
    cong f p     -> cong f applied to each step of p, likewise
    """

    if not isinstance(term, list):
        return [term]

    # Implicit arguments (`trans {y = ...} p q`) only pin down types; the
    # inferred step statements carry the same information.
    head, args = term[0], [arg for arg in term[1:] if not _is_implicit(arg)]

    if head == "trans" and len(args) == 2:
        return flatten_steps(args[0], congruences) + flatten_steps(args[1], congruences)

    if head == "sym" and len(args) == 1:
        inner = flatten_steps(args[0], congruences)
        if len(inner) > 1:
            return [_sym(step) for step in reversed(inner)]

    if head in congruences and args:
        inner = flatten_steps(args[-1], congruences)
        if len(inner) > 1:
            return [[head, *args[:-1], step] for step in inner]

    return [term]


def _is_implicit(term: Term) -> bool:
    return isinstance(term, str) and term.startswith("{") and not is_hole(term)


def is_hole(term: Term) -> bool:
    return isinstance(term, str) and term.startswith("{!")


def _sym(step: Term) -> Term:
    """sym (sym p) is just p."""

    if isinstance(step, list) and len(step) == 2 and step[0] == "sym":
        return step[1]

    return ["sym", step]


def step_head(term: Term, congruences: tuple[str, ...] = DEFAULT_CONGRUENCES) -> str:
    """The name doing the work: `sym (cong f (lemma x))` -> `lemma`."""

    while isinstance(term, list):
        head = term[0]

        if head in STRUCTURAL or head in congruences:
            term = term[-1]
            continue

        return head if isinstance(head, str) else show_term(head)

    return term


def used_names(
    term: Term, bound: set[str], congruences: tuple[str, ...] = DEFAULT_CONGRUENCES
) -> list[str]:
    """
    Global names a step relies on, in order. Variables, `trans`/`sym`, and
    the function argument of a congruence (`cong f p`: f is context, not a
    lemma) are left out, as are lambdas.
    """

    out: list[str] = []

    def walk(node: Term) -> None:
        if isinstance(node, str):
            if not (node in bound or node.startswith("{") or node.isdigit()
                    or node in STRUCTURAL or node in congruences):
                out.append(node)
            return

        head, args = node[0], node[1:]

        if head in ("λ", "\\"):
            return

        if head in congruences:
            if args:
                walk(args[-1])
            return

        walk(head)

        for arg in args:
            walk(arg)

    walk(term)

    return list(dict.fromkeys(out))


# ---------------------------------------------------------------------------
# Decomposing
# ---------------------------------------------------------------------------


def decompose(
    agda_file: Path,
    name: str,
    import_path: str = AGDA_IMPORT_PATH,
    source: str | None = None,
    congruences: tuple[str, ...] = DEFAULT_CONGRUENCES,
    declared: list[str] | tuple[str, ...] = (),
    line: int | None = None,
    timeout: int = DEPROOF_TIMEOUT_SECONDS,
) -> Decomposition:
    """
    Decompose the declaration `name` in `agda_file` (or in `source`, checked
    as that file). Every clause's right-hand side is swapped for a hole while
    Agda looks at it; the file is restored afterwards.

    Works on sketches too: a clause that is still a hole is one open step.
    `declared` names lemmas to record even if no step uses them yet (a
    sketch's lemma signatures). `line` (1-based) picks the declaration when
    the name is declared more than once in the file.
    """

    original = agda_file.read_text()
    source = original if source is None else source
    signature, clauses = parse_clauses(source, name, line)

    spans = [clause.rhs_span for clause in clauses if clause.rhs_span is not None]

    if not spans:
        # Nothing to take apart (only absurd clauses or with headers): say so
        # without asking Agda.
        return Decomposition(
            name=name, signature=signature,
            clauses=[ClauseDecomposition(lhs=c.lhs, note=c.note) for c in clauses],
        )

    holed = source

    for start, end in sorted(spans, reverse=True):
        holed = holed[:start] + "{!!}" + holed[end:]

    # Interaction points are numbered in source order on a fresh load, and
    # every clause before this one shrank to a 4-character hole.
    hole_starts = [start for start, _ in find_holes(holed)]
    goal_ids: list[int | None] = []
    shift = 0

    for clause in clauses:
        if clause.rhs_span is None:
            goal_ids.append(None)
            continue
        start, end = clause.rhs_span
        goal_ids.append(hole_starts.index(start - shift))
        shift += (end - start) - len("{!!}")

    result = Decomposition(name=name, signature=signature)
    glue: set[str] = set()

    with preserved_file(agda_file):
        agda_file.write_text(holed)

        with AgdaSession(agda_file, import_path=import_path, timeout=timeout) as session:
            load = session.load()

            if load.kind != "goal":
                raise ValueError(f"{agda_file} did not load with holes: {load.message}")

            goals = {goal.id: goal.type for goal in load.goals}

            for clause, goal_id in zip(clauses, goal_ids):
                entry = ClauseDecomposition(lhs=clause.lhs, note=clause.note)
                result.clauses.append(entry)

                if goal_id is None:
                    continue

                entry.goal = goals.get(goal_id, "")
                entry.variables, entry.variable_types, entry.hidden = _pattern_variables(
                    session, goal_id, clause.lhs
                )
                entry.steps = _steps(
                    session, goal_id, entry.goal, clause, name, congruences,
                    bound=set(entry.variables),
                )

                for step in entry.steps:
                    for lemma in step.uses:
                        if lemma in result.lemmas or lemma in glue:
                            continue

                        type_ = _infer_or(session, goal_id, lemma, "", "Instantiated")

                        # Not a lemma this proof relies on: a name Agda cannot
                        # type on its own (an infix operator such as `+`), or
                        # one whose type has unsolved metas on its own
                        # (`refl : _x ≡ _x`), i.e. a generic constructor.
                        if not type_ or META_RE.search(type_):
                            glue.add(lemma)
                            continue

                        result.lemmas[lemma] = type_
                        result.lemma_normal[lemma] = _infer_or(
                            session, goal_id, lemma, type_, "Normalised"
                        )

            any_goal = next((g for g in goal_ids if g is not None), None)

            for lemma in declared:
                if lemma in result.lemmas or any_goal is None:
                    continue
                result.lemmas[lemma] = _infer_or(session, any_goal, lemma, "?", "Instantiated")
                result.lemma_normal[lemma] = _infer_or(
                    session, any_goal, lemma, result.lemmas[lemma], "Normalised"
                )

    for clause_entry in result.clauses:
        for step in clause_entry.steps:
            step.uses = [lemma for lemma in step.uses if lemma not in glue]

    return result


def _steps(
    session: AgdaSession,
    goal_id: int,
    goal: str,
    clause: Clause,
    name: str,
    congruences: tuple[str, ...],
    bound: set[str],
) -> list[ProofStep]:
    if clause.chain is not None:
        return [_chain_step(link, bound, name, congruences) for link in clause.chain]

    try:
        terms = flatten_steps(parse_term(clause.rhs), congruences)
    except ValueError:
        # Not a term we can read (a lambda around a chain, say): one step.
        terms = [clause.rhs]

    steps: list[ProofStep] = []

    for term in terms:
        justification = show_term(term)
        # An unreadable right-hand side (kept as raw text) names nothing reliably.
        unreadable = isinstance(term, str) and any(c.isspace() for c in term)
        names = [] if unreadable else used_names(term, bound, congruences)

        # A single step is the whole clause, whose statement is its goal. An
        # open hole has no type of its own; its neighbours pin it down below.
        single = len(terms) == 1
        inferable = not (single or is_hole(term))
        statement = _infer_or(session, goal_id, justification, "") if inferable else (goal if single else "")
        normal = _infer_or(session, goal_id, justification, "", "Normalised") if inferable else ""

        steps.append(ProofStep(
            statement=statement,
            justification=justification,
            head="" if unreadable else step_head(term, congruences),
            uses=[n for n in names if n != name],
            recursive=name in names,
            normal=normal,
        ))

    _fill_from_neighbours(steps, goal)

    return steps


def _chain_step(
    link: ChainStep, bound: set[str], name: str, congruences: tuple[str, ...]
) -> ProofStep:
    """A chain step: its statement is what the author wrote, nothing inferred."""

    names: list[str] = []
    head = ""

    if link.justification:
        try:
            term = parse_term(link.justification)
        except ValueError:
            term = link.justification
        names = used_names(term, bound, congruences)
        head = step_head(term, congruences)

    return ProofStep(
        statement=f"{link.lhs} {link.relation} {link.rhs}",
        justification=link.justification,
        head=head,
        uses=[n for n in names if n != name],
        recursive=name in names,
        lhs=link.lhs,
        rhs=link.rhs,
        relation=link.relation,
        reversed=link.reversed,
    )


def _pattern_variables(
    session: AgdaSession, goal_id: int, lhs: str
) -> tuple[list[str], dict[str, str], list[str]]:
    """
    The variables a clause binds, in the order they appear on its left-hand
    side; the types of everything in context at its hole, in binding order;
    and which of those are not in scope by name. Agda's context tells
    variables from constructors (`zero`, `suc`), which the text alone cannot.
    """

    words = list(dict.fromkeys(WORD_RE.findall(lhs)[1:]))

    try:
        # as written: normalised types unfold into names the file never
        # imported, which print qualified and cannot be written back
        context = session.goal_context(goal_id, "AsIs")
    except (ValueError, TimeoutError):
        return words, {}, []

    types = {entry.name: entry.type for entry in context}
    hidden = [entry.name for entry in context if not entry.in_scope]

    return [w for w in words if w in types and w not in hidden], types, hidden


def _infer_or(
    session: AgdaSession,
    goal_id: int,
    expression: str,
    default: str,
    rewrite: str = "Simplified",
) -> str:
    try:
        return session.infer(goal_id, expression, rewrite=rewrite)
    except (ValueError, TimeoutError):
        return default


def _fill_from_neighbours(steps: list[ProofStep], goal: str) -> None:
    """
    A step inferred on its own can come back with metas (`refl : _x ≡ _x`)
    or not at all. In a chain its sides are pinned by its neighbours and the
    clause goal, so fill them in from there.
    """

    try:
        goal_lhs, goal_rhs = split_equation(goal)
    except ValueError:
        return

    def known(side: str) -> bool:
        return bool(side) and not META_RE.search(side)

    sides = [step.sides or ("", "") for step in steps]

    for index, step in enumerate(steps):
        lhs, rhs = sides[index]

        if known(lhs) and known(rhs):
            continue

        if not known(lhs):
            lhs = goal_lhs if index == 0 else sides[index - 1][1]
        if not known(rhs):
            rhs = goal_rhs if index == len(steps) - 1 else sides[index + 1][0]

        if known(lhs) and known(rhs):
            sides[index] = (lhs, rhs)
            step.statement = f"{lhs} ≡ {rhs}"


# ---------------------------------------------------------------------------
# Comparing
# ---------------------------------------------------------------------------


@dataclass
class ClauseComparison:
    pattern: str                 # canonical left-hand side
    lhs_a: str = ""
    lhs_b: str = ""
    steps_a: int = 0
    steps_b: int = 0
    shared_midpoints: list[str] = field(default_factory=list)


@dataclass
class DecompositionComparison:
    name: str
    clauses: list[ClauseComparison] = field(default_factory=list)
    # (name in a, name in b, "same" | "symmetric"), matched by normalised
    # statement: a lemma a introduced that states something b also used
    lemma_pairs: list[tuple[str, str, str]] = field(default_factory=list)
    lemmas_only_a: list[str] = field(default_factory=list)
    lemmas_only_b: list[str] = field(default_factory=list)
    # existing lemmas both proofs call, by name: shared vocabulary, not
    # shared decomposition
    shared_lemmas: list[str] = field(default_factory=list)

    @property
    def same_split(self) -> bool:
        return all(c.lhs_a and c.lhs_b for c in self.clauses)

    def render(self, label_a: str = "a", label_b: str = "b") -> str:
        lines = [f"{self.name}: case split {'matches' if self.same_split else 'differs'}"]

        for c in self.clauses:
            if not (c.lhs_a and c.lhs_b):
                side = label_a if c.lhs_a else label_b
                lines.append(f"  clause {c.lhs_a or c.lhs_b}: only in {side}")
                continue

            lines.append(
                f"  clause {c.lhs_a}: {c.steps_a} vs {c.steps_b} step(s), "
                f"{len(c.shared_midpoints)} shared midpoint(s)"
            )
            lines.extend(f"      {m}" for m in c.shared_midpoints)

        for a, b, relation in self.lemma_pairs:
            how = "same statement as" if relation == "same" else "the symmetric form of"
            lines.append(f"  lemma {a} ({label_a}) is {how} {b} ({label_b})")
        if self.shared_lemmas:
            lines.append(f"  both call: {', '.join(self.shared_lemmas)}")
        for a in self.lemmas_only_a:
            lines.append(f"  lemma {a}: only in {label_a}")
        for b in self.lemmas_only_b:
            lines.append(f"  lemma {b}: only in {label_b}")

        return "\n".join(lines)


def compare(
    a: Decomposition, b: Decomposition, introduced: set[str] | None = None
) -> DecompositionComparison:
    """
    Line up two decompositions of the same theorem. Clauses match when their
    patterns agree up to variable names; midpoints and lemma statements are
    compared in Agda's normal form, up to binder names, and a lemma also
    matches one that states the same equation the other way round. Matching
    is textual on what Agda prints, so it can miss equal statements written
    differently; it does not report false matches.

    `introduced` names the lemmas `a` stated itself (a run's drafted and
    promoted lemmas). Only those are matched by statement against `b`'s:
    that is the question whether a found the same pieces. Lemmas both merely
    call are listed as `shared_lemmas`. Without `introduced`, every lemma of
    `a` is matched by statement.
    """

    out = DecompositionComparison(name=a.name)

    def keyed(d: Decomposition) -> dict[str, tuple[ClauseDecomposition, dict[str, str]]]:
        table = {}
        for clause in d.clauses:
            renaming = {v: f"x{i}" for i, v in enumerate(clause.variables)}
            table[_rename(clause.lhs.split(None, 1)[-1], renaming)] = (clause, renaming)
        return table

    table_a, table_b = keyed(a), keyed(b)

    for pattern in list(dict.fromkeys([*table_a, *table_b])):
        entry = ClauseComparison(pattern=pattern)
        clause_a, renaming_a = table_a.get(pattern, (None, {}))
        clause_b, renaming_b = table_b.get(pattern, (None, {}))

        if clause_a:
            entry.lhs_a, entry.steps_a = clause_a.lhs, len(clause_a.steps)
        if clause_b:
            entry.lhs_b, entry.steps_b = clause_b.lhs, len(clause_b.steps)

        if clause_a and clause_b:
            mids_b = {_rename(m, renaming_b) for m in clause_b.midpoints(normal=True)}
            entry.shared_midpoints = [
                m for m in clause_a.midpoints(normal=True)
                if _rename(m, renaming_a) in mids_b
            ]

        out.clauses.append(entry)

    out.shared_lemmas = [n for n in a.lemmas if n in b.lemmas]
    candidates = {
        n: t for n, t in a.lemma_normal.items()
        if (introduced is None and n not in b.lemmas) or (introduced is not None and n in introduced)
    }
    statements_b: dict[str, str] = {}

    for name_b, type_b in b.lemma_normal.items():
        statements_b.setdefault(_canonical_statement(type_b), name_b)

    matched_b: set[str] = set()

    for name_a, type_a in candidates.items():
        same = statements_b.get(_canonical_statement(type_a))
        flipped = statements_b.get(_canonical_statement(_flip_equation(type_a)))

        if same is not None:
            out.lemma_pairs.append((name_a, same, "same"))
            matched_b.add(same)
        elif flipped is not None:
            out.lemma_pairs.append((name_a, flipped, "symmetric"))
            matched_b.add(flipped)
        else:
            out.lemmas_only_a.append(name_a)

    out.lemmas_only_b = [n for n in b.lemmas if n not in matched_b and n not in out.shared_lemmas]

    return out


def _flip_equation(type_: str) -> str:
    """`Γ → l ≡ r` -> `Γ → r ≡ l`; anything else is returned unchanged."""

    try:
        lhs, rhs = split_equation(type_)
    except ValueError:
        return type_

    # The binders end at the last top-level arrow on the left of `≡`.
    depth, cut = 0, 0

    for index, char in enumerate(lhs):
        if char in "({[":
            depth += 1
        elif char in ")}]":
            depth -= 1
        elif char == "→" and depth == 0:
            cut = index + 1

    return f"{lhs[:cut]} {rhs} ≡ {lhs[cut:].strip()}".strip()


def _rename(text: str, renaming: dict[str, str]) -> str:
    return WORD_RE.sub(lambda m: renaming.get(m.group(0), m.group(0)), text)


def _canonical_statement(type_: str) -> str:
    """Rename binders positionally: `(m n : Nat) → m + n ≡ ...` -> x0, x1."""

    binders: list[str] = []

    for group in re.findall(r"[({]([^(){}:]+):", type_) + re.findall(r"∀\s*([^→:]+)→", type_):
        binders.extend(group.split())

    renaming = {b: f"x{i}" for i, b in enumerate(dict.fromkeys(binders))}

    return " ".join(_rename(type_, renaming).split())


# ---------------------------------------------------------------------------
# Exporting sketches
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Show a finished proof as its clauses, steps and lemmas."
    )
    parser.add_argument("file", help="Agda file; relative to --checkout when one is given.")
    parser.add_argument("name", help="Declaration to take apart.")
    parser.add_argument("--line", type=int, default=None,
                        help="Line of the declaration, when its name occurs more than once.")
    parser.add_argument("--checkout", metavar="ROOT",
                        help="Library checkout FILE belongs to. Work happens in a symlink "
                             "mirror of it, so the checkout is never written to.")
    parser.add_argument("--include", default="src",
                        help="With --checkout: the include directory, relative to ROOT.")
    parser.add_argument("--import-path", default=AGDA_IMPORT_PATH,
                        help="Without --checkout: Agda's include path.")
    parser.add_argument("--agda-bin", default=None, help="Agda binary (default: $AGDA_BIN or agda).")
    parser.add_argument("--compare", metavar="OTHER_FILE",
                        help="Another file proving the same declaration name.")
    parser.add_argument("--congruence", action="append", default=[],
                        help="Extra congruence names to see through (cong always is).")
    parser.add_argument("--sketch", choices=("clause", "step", "lemma"),
                        help="Print the proof turned back into a sketch at this granularity.")
    parser.add_argument("--annotate", action="store_true",
                        help="With --sketch: comment each hole with the justification it replaced.")
    parser.add_argument("--out", help="With --sketch: also write the whole sketched file here.")
    args = parser.parse_args(argv)

    if args.agda_bin:
        config.AGDA_BIN = args.agda_bin

    congruences = DEFAULT_CONGRUENCES + tuple(args.congruence)

    if args.checkout:
        # A checkout says what it needs in its own .agda-lib; the user's
        # default libraries are for whatever Agda installed them.
        if "--no-default-libraries" not in config.AGDA_FLAGS:
            config.AGDA_FLAGS = [*config.AGDA_FLAGS, "--no-default-libraries"]

        with mirrored(Path(args.checkout), args.file) as tree:
            return _run(args, tree / args.file, str(tree / args.include), congruences)

    return _run(args, Path(args.file).resolve(), args.import_path, congruences)


def _run(
    args: argparse.Namespace, agda_file: Path, import_path: str, congruences: tuple[str, ...]
) -> int:
    first = decompose(agda_file, args.name, import_path, congruences=congruences, line=args.line)
    print(first.render())

    if args.sketch:
        from util.sketch_export import export_sketch

        sketch = export_sketch(
            agda_file, args.name, args.sketch, import_path, decomposition=first,
            annotate=args.annotate, congruences=congruences, line=args.line,
        )
        status = ("valid" if not sketch.warnings else "valid, with warnings") if sketch.valid else "INVALID"
        print(f"\n--- {args.sketch} sketch ({status}, {len(sketch.holes)} hole(s)"
              f"{', lemmas ' + ', '.join(sketch.lemmas) if sketch.lemmas else ''}) ---")
        print(sketch.excerpt)
        for problem in sketch.problems:
            print(f"problem: {problem}")
        for warning in sketch.warnings:
            print(f"warning: {warning}")
        for note in sketch.notes:
            print(f"note: {note}")
        if args.out:
            Path(args.out).write_text(sketch.source)

    if args.compare:
        second = decompose(Path(args.compare).resolve(), args.name, import_path,
                           congruences=congruences)
        print()
        print(second.render())
        print()
        print(compare(first, second).render(Path(args.file).stem, Path(args.compare).stem))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
