import argparse
from pathlib import Path

from core.proof_files import reset_helpers_file
from proof.proof_single import prove_single
from core.proof_history import ProofHistory
from core.config import DEFAULT_MODEL


DEFAULT_AGDA_FILE = Path("agda_files/Tests/Target.agda")
DEFAULT_HELPERS_FILE = Path("agda_files/Tests/Helpers.agda")
DEFAULT_HELPER_GOAL_FILE = Path("agda_files/Tests/HelperGoal.agda")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Prove one Agda target directly or by one-step decomposition."
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
        "--model",
        default=DEFAULT_MODEL,
        help="Ollama model to use.",
    )

    parser.add_argument(
        "--direct-max-attempts",
        type=int,
        default=3,
        help="Maximum direct proof attempts.",
    )

    parser.add_argument(
        "--helper-max-attempts",
        type=int,
        default=5,
        help="Maximum decomposition attempts.",
    )

    args = parser.parse_args()

    agda_file = Path(args.file)
    helpers_file = Path(args.helpers_file)

    reset_helpers_file(helpers_file)

    history = ProofHistory()
    result = prove_single(
        agda_file=agda_file,
        helpers_file=helpers_file,
        model=args.model,
        direct_max_attempts=args.direct_max_attempts,
        helper_max_attempts=args.helper_max_attempts,
        history=history,
    )

    print("\n================================")
    print("SINGLE PROOF RESULT")
    print("================================")
    print("Success:", result.success)
    print("Target:", result.target_name)

    if result.declaration is not None:
        print("\nTarget declaration:")
        print(result.declaration)

    if result.obligations:
        print("\nRemaining obligations:")
        for obligation in result.obligations:
            print(f"  {obligation.name} : {obligation.signature}")

    if result.output:
        print("\nOutput:")
        print(result.output)


if __name__ == "__main__":
    main()