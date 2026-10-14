"""
What a decomposition of a proof is: per clause of the declaration its goal
and steps (each a statement, the term justifying it, the lemmas it uses,
whether it is a recursive call), and the type of every lemma used.
`Decomposition.render()` is the text form, meant to be shown to a model.

deproof/decompose.py computes one from a finished proof (or a sketch);
deproof/comparison.py lines two of them up.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from core.agda_source import META_RE, split_equation


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
    def definitional(self) -> bool:
        """Holds by computation (`≡⟨⟩`) or `refl`: no reasoning to decompose."""
        return self.justification.strip() in ("", "refl")

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
    # Where a name comes from, as Agda says: {"what": "defined name" |
    # "constructor" | "record field" | ..., "path": file, "line": 1-based}.
    sources: dict[str, dict] = field(default_factory=dict)

    @property
    def n_steps(self) -> int:
        return sum(len(clause.steps) for clause in self.clauses)

    @property
    def n_definitional(self) -> int:
        return sum(step.definitional for clause in self.clauses for step in clause.steps)

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
            f"{len(self.clauses)} clause(s), {self.n_steps - self.n_definitional} step(s)"
            + (f" (+{self.n_definitional} by computation or refl)" if self.n_definitional else "")
            + ", "
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
            lines.extend(f"  {name} : {readable_type(type_)}" for name, type_ in self.lemmas.items())

        return "\n".join(lines)


# A module qualifier Agda prints (`Data.Nat.Base.`), up to the name it qualifies.
QUALIFIER_RE = re.compile(r"(?<![^\s(){}])(?:[A-Z][^\s(){}.]*\.)+(?=[^\s(){}.])")


def readable_type(type_: str) -> str:
    """
    A type for reading, not for checking: one line, module qualifiers dropped,
    leading implicit binders dropped. Types printed for names from opened
    records otherwise run to dozens of lines.
    """

    text = QUALIFIER_RE.sub("", " ".join(type_.split()))

    while text.startswith("{"):
        depth = 0
        for index, char in enumerate(text):
            depth += {"{": 1, "}": -1}.get(char, 0)
            if depth == 0:
                break
        rest = text[index + 1:].lstrip()
        if rest.startswith("→"):
            rest = rest[1:].lstrip()
        elif not rest.startswith("{"):
            break
        text = rest

    return text
