from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


@dataclass
class AgdaGoal:
    id: int | None
    type: str
    range: Any | None = None


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
    goal: AgdaGoal | None = None
    message: str = ""


@dataclass
class AgdaCheckResult:
    """
    Result of running plain Agda typechecking on a file.
    """

    success: bool
    output: str = ""


@dataclass
class ProofObligation:
    """
    A theorem/lemma that still needs to be proved.
    """

    name: str
    signature: str


@dataclass
class ProposedHelper:
    """
    A helper proposed by the model during decomposition.

    This is intentionally almost the same as ProofObligation, but keeping
    the name is useful when the helper is still only a proposal.
    """

    name: str
    signature: str


@dataclass
class DirectProofResult:
    """
    Result of trying to prove a target directly, without proposing helpers.

    success=True means:
        The target declaration typechecks without any new helper assumptions.
    """

    success: bool
    target_name: str
    declaration: str | None = None
    output: str = ""


@dataclass
class DecompositionResult:
    """
    Result of trying to prove a target using proposed helper assumptions.

    success=True means:
        The target declaration typechecks assuming the listed obligations.

    It does NOT mean:
        The helper obligations themselves have been proved.
    """

    success: bool
    target_name: str
    target_declaration: str | None = None
    obligations: list[ProofObligation] = field(default_factory=list)
    output: str = ""


@dataclass
class SingleProofResult:
    """
    Result of proving one target as far as possible in one layer.

    success=True means either:
        1. The target was proved directly, with no obligations left.
        2. The target was proved assuming the returned obligations.

    It does NOT mean:
        The obligations have been recursively proved.
    """

    success: bool
    target_name: str
    declaration: str | None = None
    obligations: list[ProofObligation] = field(default_factory=list)
    output: str = ""


@dataclass
class RecursiveProofResult:
    """
    Result of recursively proving a target and all helper obligations.

    success=True means:
        The target and every transitive helper obligation were fully proved.
    """

    success: bool
    target_name: str
    declaration: str | None = None
    obligations: list[ProofObligation] = field(default_factory=list)
    helper_results: list[RecursiveProofResult] = field(default_factory=list)
    output: str = ""

@dataclass
class LLMDeclResult:
    """
    Parsed result from the model when asking for one Agda declaration.
    """

    declaration: str
    full_response: str = ""


@dataclass
class LLMHelperDeclResult:
    """
    Parsed result from the model when asking for helper signatures plus
    a target declaration.
    """

    helpers: str
    declaration: str
    full_response: str = ""