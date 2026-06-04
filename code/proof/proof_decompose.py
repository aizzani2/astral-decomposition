from pathlib import Path

from core.agda_client import load_agda_and_get_first_goal, run_plain_agda
from core.llm_client import OllamaClient
from core.proof_context import (
    find_enclosing_top_level_decl_name,
    get_signature_line,
    get_start_line_from_range,
)
from core.proof_files import restore_file, save_file, write_postulated_helpers_file
from core.proof_history import ProofHistory
from core.proof_state import DecompositionResult
from util.helper_utils import parse_helper_signatures, proposed_helpers_to_obligations
from util.source_edit import ensure_import, replace_top_level_decl, validate_declaration_name


MODEL = "qwen2.5-coder:7b"
HELPER_MAX_ATTEMPTS = 5

HELPERS_IMPORT = "open import Tests.Helpers"


def decompose_once(
    agda_file: Path,
    helpers_file: Path,
    expected_target_name: str | None = None,
    model: str = MODEL,
    max_attempts: int = HELPER_MAX_ATTEMPTS,
    history: ProofHistory | None = None,
) -> DecompositionResult:
    """
    Try to prove the declaration containing the first hole by proposing helpers.

    This function checks whether the target can be proved assuming the proposed
    helpers are postulated in helpers_file.

    success=True means:
        The target declaration typechecks assuming the returned obligations.

    It does NOT mean:
        The helper obligations themselves have been proved.
    """
    if history is None:
        history = ProofHistory()

    original_source = save_file(agda_file)
    original_helpers = save_file(helpers_file)

    if original_source is None:
        message = f"File does not exist: {agda_file}"

        return DecompositionResult(
            success=False,
            target_name="<unknown>",
            output=message,
        )

    load_result = load_agda_and_get_first_goal(agda_file)

    if load_result.kind == "error":
        message = f"Agda found an error before getting to a hole:\n{load_result.message}"

        return DecompositionResult(
            success=False,
            target_name=expected_target_name or "<unknown>",
            output=message,
        )

    if load_result.kind == "no-goals":
        check_result = run_plain_agda(agda_file)

        return DecompositionResult(
            success=check_result.success,
            target_name=expected_target_name or "<none>",
            output=check_result.output,
        )

    if load_result.goal is None:
        return DecompositionResult(
            success=False,
            target_name=expected_target_name or "<unknown>",
            output="Agda returned kind='goal' but no goal object.",
        )

    goal = load_result.goal

    if goal.range is None:
        return DecompositionResult(
            success=False,
            target_name=expected_target_name or "<unknown>",
            output="No range found for the first goal.",
        )

    hole_line = get_start_line_from_range(goal.range)

    target_name = find_enclosing_top_level_decl_name(
        source=original_source,
        hole_line=hole_line,
    )

    if expected_target_name is not None and target_name != expected_target_name:
        message = (
            "The first hole appears to be inside a different declaration than expected.\n"
            f"Expected: {expected_target_name}\n"
            f"Found:    {target_name}"
        )

        return DecompositionResult(
            success=False,
            target_name=target_name,
            output=message,
        )

    expected_signature = get_signature_line(original_source, target_name)

    llm = OllamaClient(model=model)
    previous_errors = history.messages_for_target(target_name)

    for attempt in range(1, max_attempts + 1):
        print(f"\n=== Decomposition attempt {attempt} for {target_name} ===")
        print("Goal type:")
        print(goal.type)

        try:
            result = llm.ask_for_helpers_and_declaration(
                source=original_source,
                target_name=target_name,
                goal_type=goal.type,
                previous_errors=previous_errors,
            )

            print("\nParsed helper block:")
            print(result.helpers)

            print("\nParsed target declaration:")
            print(result.declaration)

            validate_declaration_name(result.declaration, target_name)

            actual_first_line = result.declaration.strip().splitlines()[0].strip()

            if actual_first_line != expected_signature:
                raise ValueError(
                    "The LLM changed the target type signature.\n"
                    f"Expected: {expected_signature}\n"
                    f"Got:      {actual_first_line}"
                )

            proposed_helpers = parse_helper_signatures(result.helpers)
            obligations = proposed_helpers_to_obligations(proposed_helpers)

        except ValueError as e:
            print("\nCould not parse or validate LLM response:")
            print(e)

            previous_errors.append(
                f"""
Your previous response could not be parsed or validated.

Error:
{e}

Required format:

<AGDA_HELPERS>
helper signatures here
</AGDA_HELPERS>

<AGDA_DECL>
target declaration here
</AGDA_DECL>

The first line inside <AGDA_DECL> must be exactly:

{expected_signature}

Do not change the target type signature.
"""
            )
            continue

        print("\nParsed helpers:")
        for helper in proposed_helpers:
            print(f"  {helper.name} : {helper.signature}")

        write_postulated_helpers_file(
            helpers_file=helpers_file,
            helpers=proposed_helpers,
        )

        source_with_import = ensure_import(
            source=original_source,
            import_line=HELPERS_IMPORT,
        )

        trial_source = replace_top_level_decl(
            source=source_with_import,
            name=target_name,
            replacement=result.declaration,
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

            return DecompositionResult(
                success=True,
                target_name=target_name,
                target_declaration=result.declaration,
                obligations=obligations,
                output=check_result.output,
            )

        history.add(
            phase="decomposition",
            target_name=target_name,
            candidate=(
                "Helper signatures:\n"
                f"{result.helpers}\n\n"
                "Target declaration:\n"
                f"{result.declaration}"
            ),
            agda_output=check_result.output,
        )

        previous_errors = history.messages_for_target(target_name)

        restore_file(helpers_file, original_helpers)

    restore_file(agda_file, original_source)
    restore_file(helpers_file, original_helpers)

    return DecompositionResult(
        success=False,
        target_name=target_name,
        output=f"Failed to decompose/prove {target_name} using helper assumptions.",
    )


def truncate_error(output: str, max_chars: int = 4000) -> str:
    if len(output) <= max_chars:
        return output

    return output[:max_chars] + "\n\n... truncated ..."