from pathlib import Path

from core.agda_client import run_plain_agda
from core.proof_files import (
    append_helper_declaration,
    reset_helpers_file,
    restore_file,
    save_file,
    write_helper_goal_file,
)
from core.proof_history import ProofHistory
from core.proof_state import ProofObligation, RecursiveProofResult
from proof.proof_single import prove_single


MODEL = "qwen2.5-coder:7b"
DIRECT_MAX_ATTEMPTS = 3
HELPER_MAX_ATTEMPTS = 5
MAX_DEPTH = 5


def prove_recursive(
    agda_file: Path,
    helpers_file: Path,
    helper_goal_file: Path,
    model: str = MODEL,
    direct_max_attempts: int = DIRECT_MAX_ATTEMPTS,
    helper_max_attempts: int = HELPER_MAX_ATTEMPTS,
    max_depth: int = MAX_DEPTH,
    depth: int = 0,
    history: ProofHistory | None = None,
) -> RecursiveProofResult:
    """
    Recursively prove the declaration containing the first hole.

    success=True means:
        The target and all transitive helper obligations were proved.
    """
    if history is None:
        history = ProofHistory()

    if depth > max_depth:
        return RecursiveProofResult(
            success=False,
            target_name="<max-depth>",
            output=f"Maximum recursive proof depth exceeded: {max_depth}",
        )

    original_source = save_file(agda_file)
    original_helpers = save_file(helpers_file)

    if original_source is None:
        return RecursiveProofResult(
            success=False,
            target_name="<unknown>",
            output=f"File does not exist: {agda_file}",
        )

    single = prove_single(
        agda_file=agda_file,
        helpers_file=helpers_file,
        model=model,
        direct_max_attempts=direct_max_attempts,
        helper_max_attempts=helper_max_attempts,
        history=history,
    )

    if not single.success:
        restore_file(agda_file, original_source)
        restore_file(helpers_file, original_helpers)

        return RecursiveProofResult(
            success=False,
            target_name=single.target_name,
            declaration=single.declaration,
            obligations=single.obligations,
            output=single.output,
        )

    if not single.obligations:
        return RecursiveProofResult(
            success=True,
            target_name=single.target_name,
            declaration=single.declaration,
            obligations=[],
            helper_results=[],
            output=single.output,
        )

    # At this point:
    #   - agda_file has the target proof that uses helpers
    #   - helpers_file may contain postulated helpers
    #
    # But for recursive proving, we do NOT want helpers_file to contain
    # the current obligations as postulates. We reset it and only append
    # real proved helper declarations.
    target_source_with_helper_proof = agda_file.read_text()

    reset_helpers_file(helpers_file)

    helper_results: list[RecursiveProofResult] = []

    for obligation in single.obligations:
        helper_result = prove_helper_obligation(
            obligation=obligation,
            helpers_file=helpers_file,
            helper_goal_file=helper_goal_file,
            model=model,
            direct_max_attempts=direct_max_attempts,
            helper_max_attempts=helper_max_attempts,
            max_depth=max_depth,
            depth=depth + 1,
            history=history,
        )

        if not helper_result.success:
            restore_file(agda_file, original_source)
            restore_file(helpers_file, original_helpers)

            return RecursiveProofResult(
                success=False,
                target_name=single.target_name,
                declaration=single.declaration,
                obligations=single.obligations,
                helper_results=helper_results + [helper_result],
                output=(
                    f"Failed to prove helper obligation {obligation.name}.\n\n"
                    f"{helper_result.output}"
                ),
            )

        if helper_result.declaration is None:
            restore_file(agda_file, original_source)
            restore_file(helpers_file, original_helpers)

            return RecursiveProofResult(
                success=False,
                target_name=single.target_name,
                declaration=single.declaration,
                obligations=single.obligations,
                helper_results=helper_results + [helper_result],
                output=f"Helper {obligation.name} succeeded but returned no declaration.",
            )

        append_helper_declaration(
            helpers_file=helpers_file,
            declaration=helper_result.declaration,
        )

        helper_results.append(helper_result)

    agda_file.write_text(target_source_with_helper_proof)

    final_check = run_plain_agda(agda_file)

    if not final_check.success:
        restore_file(agda_file, original_source)
        restore_file(helpers_file, original_helpers)

        return RecursiveProofResult(
            success=False,
            target_name=single.target_name,
            declaration=single.declaration,
            obligations=single.obligations,
            helper_results=helper_results,
            output=(
                "All helpers were individually proved, but the final target check failed.\n\n"
                f"{final_check.output}"
            ),
        )

    return RecursiveProofResult(
        success=True,
        target_name=single.target_name,
        declaration=single.declaration,
        obligations=single.obligations,
        helper_results=helper_results,
        output=final_check.output,
    )


def prove_helper_obligation(
    obligation: ProofObligation,
    helpers_file: Path,
    helper_goal_file: Path,
    model: str,
    direct_max_attempts: int,
    helper_max_attempts: int,
    max_depth: int,
    depth: int,
    history: ProofHistory,
) -> RecursiveProofResult:
    """
    Turn one helper obligation into a temporary Agda goal, then recursively
    prove that goal.
    """

    write_helper_goal_file(
        helper_goal_file=helper_goal_file,
        obligation=obligation,
    )

    return prove_recursive(
        agda_file=helper_goal_file,
        helpers_file=helpers_file,
        helper_goal_file=helper_goal_file,
        model=model,
        direct_max_attempts=direct_max_attempts,
        helper_max_attempts=helper_max_attempts,
        max_depth=max_depth,
        depth=depth,
        history=history,
    )