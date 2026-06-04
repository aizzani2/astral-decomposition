from pathlib import Path

from core.agda_client import load_agda_and_get_first_goal, run_plain_agda
from core.llm_client import OllamaClient
from core.proof_context import (
    find_enclosing_top_level_decl_name,
    get_signature_line,
    get_start_line_from_range,
)
from core.proof_files import restore_file, save_file
from core.proof_history import ProofHistory
from core.proof_state import DirectProofResult
from util.source_edit import replace_top_level_decl, validate_declaration_name


MODEL = "qwen2.5-coder:7b"
DIRECT_MAX_ATTEMPTS = 3


def prove_direct(
    agda_file: Path,
    model: str = MODEL,
    max_attempts: int = DIRECT_MAX_ATTEMPTS,
    history: ProofHistory | None = None,
) -> DirectProofResult:
    """
    Try to prove the declaration containing the first hole directly.

    This function does not propose helpers, does not postulate anything,
    and does not recurse.

    success=True means:
        The returned declaration typechecks directly in the original file.
    """
    if history is None:
        history = ProofHistory()
    
    original_source = save_file(agda_file)
    
    if original_source is None:
        message = f"File does not exist: {agda_file}"

        return DirectProofResult(
            success=False,
            target_name="<unknown>",
            output=message,
        )

    load_result = load_agda_and_get_first_goal(agda_file)

    if load_result.kind == "error":
        message = f"Agda found an error before getting to a hole:\n{load_result.message}"

        return DirectProofResult(
            success=False,
            target_name="<unknown>",
            output=message,
        )

    if load_result.kind == "no-goals":
        check_result = run_plain_agda(agda_file)

        return DirectProofResult(
            success=check_result.success,
            target_name="<none>",
            output=check_result.output,
        )

    if load_result.goal is None:
        return DirectProofResult(
            success=False,
            target_name="<unknown>",
            output="Agda returned kind='goal' but no goal object.",
        )

    goal = load_result.goal

    if goal.range is None:
        return DirectProofResult(
            success=False,
            target_name="<unknown>",
            output="No range found for the first goal.",
        )

    hole_line = get_start_line_from_range(goal.range)

    target_name = find_enclosing_top_level_decl_name(
        source=original_source,
        hole_line=hole_line,
    )

    expected_signature = get_signature_line(original_source, target_name)

    llm = OllamaClient(model=model)
    previous_errors = history.messages_for_target(target_name)

    for attempt in range(1, max_attempts + 1):
        print(f"\n=== Direct proof attempt {attempt} for {target_name} ===")
        print("Goal type:")
        print(goal.type)

        try:
            declaration = llm.ask_for_direct_declaration(
                source=original_source,
                target_name=target_name,
                goal_type=goal.type,
                previous_errors=previous_errors,
            )

            print("\nParsed declaration:")
            print(declaration)

            validate_declaration_name(declaration, target_name)

            actual_first_line = declaration.strip().splitlines()[0].strip()

            if actual_first_line != expected_signature:
                raise ValueError(
                    "The LLM changed the target type signature.\n"
                    f"Expected: {expected_signature}\n"
                    f"Got:      {actual_first_line}"
                )

        except ValueError as e:
            print("\nCould not parse or validate LLM response:")
            print(e)

            previous_errors.append(
                f"""
Your previous response could not be parsed or validated.

Error:
{e}

The declaration must begin with exactly:

{expected_signature}

Do not change the target type signature.
"""
            )
            continue

        trial_source = replace_top_level_decl(
            source=original_source,
            name=target_name,
            replacement=declaration,
        )

        agda_file.write_text(trial_source)

        try:
            check_result = run_plain_agda(agda_file)
        finally:
            restore_file(agda_file, original_source)

        print("\nAgda output:")
        print(check_result.output)

        if check_result.success:
            agda_file.write_text(trial_source)

            return DirectProofResult(
                success=True,
                target_name=target_name,
                declaration=declaration,
                output=check_result.output,
            )

        history.add(
            phase="direct",
            target_name=target_name,
            candidate=declaration,
            agda_output=check_result.output,
        )

        previous_errors = history.messages_for_target(target_name)

    restore_file(agda_file, original_source)

    return DirectProofResult(
        success=False,
        target_name=target_name,
        output=f"Failed to prove {target_name} directly.",
    )


def truncate_error(output: str, max_chars: int = 4000) -> str:
    if len(output) <= max_chars:
        return output

    return output[:max_chars] + "\n\n... truncated ..."