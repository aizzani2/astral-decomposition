from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


# ---------------------------------------------------------------------------
# Agda interaction
# ---------------------------------------------------------------------------


@dataclass
class ContextEntry:
    """One binding visible at a hole, e.g. `n : Nat`."""

    name: str
    type: str
    in_scope: bool = True


@dataclass
class AgdaGoal:
    id: int | None
    type: str
    range: Any | None = None
    context: list[ContextEntry] = field(default_factory=list)


@dataclass
class AgdaLoadResult:
    """
    Result of loading an Agda file through the interaction protocol.

    kind meanings:
        "error"    = Agda failed before producing goals.
        "no-goals" = The file loaded successfully and has no holes.
        "goal"     = The file loaded successfully and has at least one goal.
    """

    kind: str
    goals: list[AgdaGoal] = field(default_factory=list)
    message: str = ""
    warnings: list[str] = field(default_factory=list)

    @property
    def goal(self) -> AgdaGoal | None:
        """First goal, kept so older single-goal call sites keep working."""
        return self.goals[0] if self.goals else None


@dataclass
class AgdaCheckResult:
    """Result of running plain Agda typechecking on a file."""

    success: bool
    output: str = ""
    timed_out: bool = False


@dataclass
class SketchCheckResult:
    """
    Result of typechecking a *sketch*: a file that is allowed to contain holes.

    kind meanings:
        "error"      = real type error; the skeleton itself is wrong.
        "holes"      = skeleton typechecks, N interaction points remain.
        "complete"   = skeleton typechecks and has no holes left.
    """

    kind: str
    goals: list[AgdaGoal] = field(default_factory=list)
    message: str = ""

    @property
    def structurally_valid(self) -> bool:
        return self.kind in ("holes", "complete")


# ---------------------------------------------------------------------------
# Informal layer (the "Draft" stage)
# ---------------------------------------------------------------------------


@dataclass
class InformalStep:
    """
    One delineated step of an informal proof.

    kind:
        "step"      = an ordinary inline reasoning step
        "case"      = a case split / pattern match
        "induction" = an induction skeleton
        "lemma"     = a step large enough to be broken out as its own lemma

    hard=True marks a step the drafter thinks needs its own lemma and its own
    recursive proof attempt, rather than being closed by a hammer.
    """

    index: int
    text: str
    kind: str = "step"
    hard: bool = False
    lemma_name: str | None = None


@dataclass
class InformalProof:
    statement: str
    steps: list[InformalStep] = field(default_factory=list)
    raw: str = ""

    def as_numbered_text(self) -> str:
        return "\n".join(
            f"{step.index}. [{step.kind}{'/hard' if step.hard else ''}] {step.text}"
            for step in self.steps
        )


# ---------------------------------------------------------------------------
# Formal sketch layer (the "Sketch" stage)
# ---------------------------------------------------------------------------


@dataclass
class ProofObligation:
    """A theorem/lemma that still needs to be proved."""

    name: str
    signature: str
    informal_hint: str = ""


@dataclass
class ProposedHelper:
    """A helper proposed by the model during decomposition."""

    name: str
    signature: str
    informal_hint: str = ""


@dataclass
class SketchGap:
    """
    One open conjecture in a formal sketch: a hole plus everything we know
    about it.

    hole_index is the 0-based position of the hole in the source text, which
    matches the order Agda assigns interaction point ids on a fresh load.
    """

    hole_index: int
    goal_id: int | None = None
    goal_type: str = ""
    context: list[ContextEntry] = field(default_factory=list)
    informal_hint: str = ""

    def context_text(self) -> str:
        return "\n".join(f"  {entry.name} : {entry.type}" for entry in self.context)


@dataclass
class FormalSketch:
    """
    A skeleton proof of the target: correct structure, holes where the work is.

    `source` is the full text of the target file with holes still in it.
    `lemmas` are the broken-out hard steps, postulated while the skeleton is
    being checked and discharged recursively afterwards.
    """

    target_name: str
    signature: str
    source: str
    lemmas: list[ProofObligation] = field(default_factory=list)
    gaps: list[SketchGap] = field(default_factory=list)
    raw_response: str = ""


@dataclass
class GapResult:
    """Result of trying to close one hole in a sketch."""

    success: bool
    gap: SketchGap
    solution: str | None = None
    method: str = ""  # "mimer" | "tactic:refl" | "llm" | "lemma" | "failed"
    output: str = ""


# ---------------------------------------------------------------------------
# Results
# ---------------------------------------------------------------------------


@dataclass
class DirectProofResult:
    success: bool
    target_name: str
    declaration: str | None = None
    output: str = ""


@dataclass
class DecompositionResult:
    """
    success=True means the target typechecks *assuming* the listed obligations.
    It does NOT mean the obligations have been proved.
    """

    success: bool
    target_name: str
    target_declaration: str | None = None
    obligations: list[ProofObligation] = field(default_factory=list)
    output: str = ""


@dataclass
class SingleProofResult:
    success: bool
    target_name: str
    declaration: str | None = None
    obligations: list[ProofObligation] = field(default_factory=list)
    output: str = ""


@dataclass
class RecursiveProofResult:
    success: bool
    target_name: str
    declaration: str | None = None
    obligations: list[ProofObligation] = field(default_factory=list)
    helper_results: list[RecursiveProofResult] = field(default_factory=list)
    output: str = ""


@dataclass
class DSPResult:
    """
    Result of the full draft -> sketch -> prove pipeline for one target.

    success=True means the target file typechecks with no holes and no
    remaining postulates.
    """

    success: bool
    target_name: str
    informal: InformalProof | None = None
    sketch: FormalSketch | None = None
    gap_results: list[GapResult] = field(default_factory=list)
    lemma_results: list[DSPResult] = field(default_factory=list)
    final_source: str | None = None
    output: str = ""

    def gaps_closed(self) -> tuple[int, int]:
        closed = sum(1 for r in self.gap_results if r.success)
        return closed, len(self.gap_results)


# ---------------------------------------------------------------------------
# LLM parse results
# ---------------------------------------------------------------------------


@dataclass
class LLMDeclResult:
    declaration: str
    full_response: str = ""


@dataclass
class LLMHelperDeclResult:
    helpers: str
    declaration: str
    full_response: str = ""
