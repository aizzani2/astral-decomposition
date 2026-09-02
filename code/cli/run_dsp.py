import argparse
from pathlib import Path

from core.config import (
    AGDA_ROOT,
    AGDA_IMPORT_PATH,
    DEFAULT_MODEL,
    GAP_LLM_ATTEMPTS,
    MAX_DEPTH,
    OLLAMA_BASE_URL,
    SKETCH_MAX_ATTEMPTS,
    PROJECT_ROOT,
)
from core.hammer import HammerConfig
from core.llm_client import OllamaBackend, ProofLLM
from core.proof_files import reset_helpers_file
from core.proof_history import ProofHistory
from core.proof_state import DSPResult
from proof.proof_sketch import prove_dsp


DEFAULT_AGDA_FILE = AGDA_ROOT / "Tests" / "Target.agda"
DEFAULT_HELPERS_FILE = AGDA_ROOT / "Tests" / "Helpers.agda"
DEFAULT_HELPER_GOAL_FILE = AGDA_ROOT / "Tests" / "HelperGoal.agda"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Draft an informal proof, sketch it in Agda, then close the gaps."
    )

    parser.add_argument("--file", default=str(DEFAULT_AGDA_FILE))
    parser.add_argument("--helpers-file", default=str(DEFAULT_HELPERS_FILE))
    parser.add_argument("--helper-goal-file", default=str(DEFAULT_HELPER_GOAL_FILE))
    parser.add_argument("--model", default=DEFAULT_MODEL)
    parser.add_argument("--base-url", default=OLLAMA_BASE_URL)
    parser.add_argument("--import-path", default=AGDA_IMPORT_PATH)

    parser.add_argument(
        "--informal-statement",
        default=None,
        help="Natural-language statement. Defaults to the Agda signature.",
    )
    parser.add_argument(
        "--informal-proof",
        default=None,
        help="Path to a human-written informal proof, skipping the draft stage.",
    )

    parser.add_argument("--sketch-max-attempts", type=int, default=SKETCH_MAX_ATTEMPTS)
    parser.add_argument("--gap-llm-attempts", type=int, default=GAP_LLM_ATTEMPTS)
    parser.add_argument("--max-depth", type=int, default=MAX_DEPTH)
    parser.add_argument("--no-mimer", action="store_true", help="Skip Agda's auto.")
    parser.add_argument("--quiet", action="store_true")

    args = parser.parse_args()

    informal_proof_text = None

    if args.informal_proof:
        informal_proof_text = Path(args.informal_proof).read_text()

    helpers_file = Path(args.helpers_file)
    reset_helpers_file(helpers_file)

    llm = ProofLLM(
        backend=OllamaBackend(model=args.model, base_url=args.base_url),
    )

    result = prove_dsp(
        agda_file=Path(args.file),
        helpers_file=helpers_file,
        helper_goal_file=Path(args.helper_goal_file),
        informal_statement=args.informal_statement,
        informal_proof_text=informal_proof_text,
        llm=llm,
        model=args.model,
        sketch_max_attempts=args.sketch_max_attempts,
        hammer=HammerConfig(
            use_mimer=not args.no_mimer,
            llm_attempts=args.gap_llm_attempts,
            import_path=args.import_path,
        ),
        max_depth=args.max_depth,
        history=ProofHistory(),
        verbose=not args.quiet,
    )

    report(result)

    if result.success and result.final_source:
        out_dir = PROJECT_ROOT / "proofs"
        out_dir.mkdir(exist_ok=True)
        out_path = out_dir / f"{result.target_name}.agda"
        out_path.write_text(result.final_source)
        print(f"\nProof written to {out_path}")


def report(result: DSPResult, indent: int = 0) -> None:
    prefix = " " * indent

    if indent == 0:
        print("\n================================")
        print("DSP RESULT")
        print("================================")

    closed, total = result.gaps_closed()

    print(f"{prefix}Target:  {result.target_name}")
    print(f"{prefix}Success: {result.success}")
    print(f"{prefix}Gaps:    {closed}/{total} closed")

    if result.informal is not None:
        print(f"{prefix}Informal steps:")
        for step in result.informal.steps:
            print(f"{prefix}  {step.index}. [{step.kind}] {step.text}")

    for gap_result in sorted(result.gap_results, key=lambda r: r.gap.hole_index):
        status = gap_result.solution if gap_result.success else "UNSOLVED"
        print(
            f"{prefix}  hole {gap_result.gap.hole_index} "
            f"({gap_result.method}): {status}"
        )

    if result.lemma_results:
        print(f"{prefix}Lemmas:")
        for lemma_result in result.lemma_results:
            report(lemma_result, indent=indent + 4)

    if result.final_source and indent == 0:
        print("\nFinal proof:\n")
        print(result.final_source)

    if result.output and not result.success:
        print(f"\n{prefix}Output:\n{prefix}{result.output}")


if __name__ == "__main__":
    main()
