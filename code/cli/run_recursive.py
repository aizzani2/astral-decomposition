import argparse
from pathlib import Path

from core.proof_files import reset_helpers_file
from proof.proof_recursive import prove_recursive
from core.proof_history import ProofHistory
from core.config import DEFAULT_MODEL


DEFAULT_AGDA_FILE = Path("agda_files/Tests/Target.agda")
DEFAULT_HELPERS_FILE = Path("agda_files/Tests/Helpers.agda")
DEFAULT_HELPER_GOAL_FILE = Path("agda_files/Tests/HelperGoal.agda")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Recursively prove an Agda target and all helper obligations."
    )

    parser.add_argument(
        "--file",
        default=str(DEFAULT_AGDA_FILE),
        help="Agda file to prove, default: Tests/Target.agda",
    )

    parser.add_argument(
        "--helpers-file",
        default=str(DEFAULT_HELPERS_FILE),
        help="Helpers file to use, default: Tests/Helpers.agda",
    )

    parser.add_argument(
        "--helper-goal-file",
        default=str(DEFAULT_HELPER_GOAL_FILE),
        help="Temporary helper goal file, default: Tests/HelperGoal.agda",
    )

    parser.add_argument(
        "--model",
        default=DEFAULT_MODEL,
        help="Ollama model to use.",
    )

    parser.add_argument(
        "--direct-max-attempts",
        type=int,
        default=3,
        help="Maximum direct proof attempts per obligation.",
    )

    parser.add_argument(
        "--helper-max-attempts",
        type=int,
        default=5,
        help="Maximum decomposition attempts per obligation.",
    )

    parser.add_argument(
        "--max-depth",
        type=int,
        default=5,
        help="Maximum recursive helper proof depth.",
    )

    args = parser.parse_args()

    agda_file = Path(args.file)
    helpers_file = Path(args.helpers_file)
    helper_goal_file = Path(args.helper_goal_file)

    reset_helpers_file(helpers_file)

    history = ProofHistory()
    result = prove_recursive(
        agda_file=agda_file,
        helpers_file=helpers_file,
        helper_goal_file=helper_goal_file,
        model=args.model,
        direct_max_attempts=args.direct_max_attempts,
        helper_max_attempts=args.helper_max_attempts,
        max_depth=args.max_depth,
        history=history,
    )

    print("\n================================")
    print("RECURSIVE PROOF RESULT")
    print("================================")
    print("Success:", result.success)
    print("Target:", result.target_name)

    if result.declaration is not None:
        print("\nTarget declaration:")
        print(result.declaration)

    if result.obligations:
        print("\nObligations:")
        for obligation in result.obligations:
            print(f"  {obligation.name} : {obligation.signature}")

    if result.helper_results:
        print("\nHelper results:")
        print_recursive_helper_results(result.helper_results, indent=2)

    if result.output:
        print("\nOutput:")
        print(result.output)


def print_recursive_helper_results(helper_results, indent: int = 0) -> None:
    prefix = " " * indent

    for helper_result in helper_results:
        status = "success" if helper_result.success else "failed"
        print(f"{prefix}- {helper_result.target_name}: {status}")

        if helper_result.declaration is not None:
            declaration_first_line = helper_result.declaration.strip().splitlines()[0]
            print(f"{prefix}  {declaration_first_line}")

        if helper_result.obligations:
            print(f"{prefix}  obligations:")
            for obligation in helper_result.obligations:
                print(f"{prefix}    {obligation.name} : {obligation.signature}")

        if helper_result.helper_results:
            print_recursive_helper_results(
                helper_result.helper_results,
                indent=indent + 4,
            )


if __name__ == "__main__":
    main()