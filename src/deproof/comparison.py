"""
Lining up two decompositions of the same theorem (deproof/decomposition.py):
a run's against the library's, or two runs'. Clauses match by pattern up to
variable names; shared midpoints and lemma statements are compared in Agda's
normal form; a run's own lemmas are matched against the other side's by
statement, an equation also matching its flip.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from core.agda_source import WORD_RE, split_equation
from deproof.decomposition import ClauseDecomposition, Decomposition


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


def match_statements(found: dict[str, str], wanted: dict[str, str]) -> list[tuple[str, str, str]]:
    """
    (found name, wanted name, "same" | "symmetric") for each statement in
    `wanted` that one in `found` states, up to binder names; both in Agda's
    normal form. Used to tell whether a run recovered lemmas it was not shown.
    """

    by_statement: dict[str, str] = {}
    for name, type_ in found.items():
        if type_:
            by_statement.setdefault(_canonical_statement(type_), name)

    pairs = []
    for name, type_ in wanted.items():
        if not type_:
            continue
        same = by_statement.get(_canonical_statement(type_))
        flipped = by_statement.get(_canonical_statement(_flip_equation(type_)))
        if same is not None:
            pairs.append((same, name, "same"))
        elif flipped is not None:
            pairs.append((flipped, name, "symmetric"))

    return pairs


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
