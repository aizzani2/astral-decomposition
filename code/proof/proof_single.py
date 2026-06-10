from pathlib import Path

from proof.proof_decompose import decompose_once
from proof.proof_direct import prove_direct
from core.proof_history import ProofHistory
from core.proof_state import SingleProofResult
from core.config import DEFAULT_MODEL, DIRECT_MAX_ATTEMPTS, HELPER_MAX_ATTEMPTS


def prove_single(
    agda_file: Path,
    helpers_file: Path,
    model: str = DEFAULT_MODEL,
    direct_max_attempts: int = DIRECT_MAX_ATTEMPTS,
    helper_max_attempts: int = HELPER_MAX_ATTEMPTS,
    history: ProofHistory | None = None,
) -> SingleProofResult:
    """
    Try to prove one target declaration.

    Strategy:
        1. Try a direct proof.
        2. If direct proof fails, try one-step decomposition.

    success=True means either:
        - the target was proved directly, with no obligations left; or
        - the target was proved assuming the returned obligations.

    It does NOT mean:
        The returned obligations have been recursively proved.
    """
    if history is None:
        history = ProofHistory()

    direct_result = prove_direct(
        agda_file=agda_file,
        model=model,
        max_attempts=direct_max_attempts,
        history=history,
    )

    if direct_result.success:
        return SingleProofResult(
            success=True,
            target_name=direct_result.target_name,
            declaration=direct_result.declaration,
            obligations=[],
            output=direct_result.output,
        )

    target_name = direct_result.target_name

    if target_name in ("<unknown>", "<none>"):
        target_name = None

    decomposition_result = decompose_once(
        agda_file=agda_file,
        helpers_file=helpers_file,
        expected_target_name=target_name,
        model=model,
        max_attempts=helper_max_attempts,
        history=history,
    )

    if not decomposition_result.success:
        return SingleProofResult(
            success=False,
            target_name=decomposition_result.target_name,
            declaration=decomposition_result.target_declaration,
            obligations=decomposition_result.obligations,
            output=(
                "Direct proof failed and decomposition also failed.\n\n"
                "Direct proof output:\n"
                f"{direct_result.output}\n\n"
                "Decomposition output:\n"
                f"{decomposition_result.output}"
            ),
        )

    return SingleProofResult(
        success=True,
        target_name=decomposition_result.target_name,
        declaration=decomposition_result.target_declaration,
        obligations=decomposition_result.obligations,
        output=decomposition_result.output,
    )