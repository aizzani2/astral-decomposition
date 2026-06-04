import argparse
from pathlib import Path

from proof.proof_direct import prove_direct

DEFAULT_AGDA_FILE = Path("agda_files/Tests/Target.agda")
DEFAULT_HELPERS_FILE = Path("agda_files/Tests/Helpers.agda")
DEFAULT_HELPER_GOAL_FILE = Path("agda_files/Tests/HelperGoal.agda")

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Try to prove one Agda target directly, without helper lemmas."
    )

    parser.add_argument(
        "--file",
        default=str(DEFAULT_AGDA_FILE),
        help="Agda file to prove, default: Tests/Target.agda",
    )

    parser.add_argument(
        "--model",
        default="qwen2.5-coder:7b",
        help="Ollama model to use.",
    )

    parser.add_argument(
        "--max-attempts",
        type=int,
        default=3,
        help="Maximum direct proof attempts.",
    )

    args = parser.parse_args()

    result = prove_direct(
        agda_file=Path(args.file),
        model=args.model,
        max_attempts=args.max_attempts,
    )

    print("\n================================")
    print("DIRECT PROOF RESULT")
    print("================================")
    print("Success:", result.success)
    print("Target:", result.target_name)

    if result.declaration is not None:
        print("\nTarget declaration:")
        print(result.declaration)

    if result.output:
        print("\nOutput:")
        print(result.output)


if __name__ == "__main__":
    main()