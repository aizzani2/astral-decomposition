import argparse
import shutil
import sys
import time
from pathlib import Path

from core import config
from core.config import (
    AGDA_ROOT,
    AGDA_IMPORT_PATH,
    DEFAULT_BACKEND,
    DEFAULT_MODEL,
    DRAFT_SAMPLES,
    GAP_LLM_ATTEMPTS,
    MAX_DEPTH,
    MIMER_TIMEOUT_SECONDS,
    OLLAMA_BASE_URL,
    RUNS_ROOT,
    SKETCH_MAX_ATTEMPTS,
    PROJECT_ROOT,
)
from core.hammer import HammerConfig
from core.llm_client import OllamaBackend, ProofLLM, make_backend
from core.proof_files import reset_helpers_file
from core.proof_history import ProofHistory
from core.proof_state import DSPResult
from core.run_log import RunLogger, run_logger, set_run_logger
from proof.formalizer import FormalizerLLM
from proof.proof_sketch import log_decomposition, prove_dsp
from util.deproof import compare


DEFAULT_AGDA_FILE = AGDA_ROOT / "Tests" / "Target.agda"
DEFAULT_HELPERS_FILE = AGDA_ROOT / "Tests" / "Helpers.agda"
DEFAULT_HELPER_GOAL_FILE = AGDA_ROOT / "Tests" / "HelperGoal.agda"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Draft an informal proof, sketch it in Agda, then close the gaps."
    )

    parser.add_argument("--file", default=str(DEFAULT_AGDA_FILE))
    parser.add_argument("--helpers-file", default=str(DEFAULT_HELPERS_FILE))
    parser.add_argument("--helper-goal-file", default=str(DEFAULT_HELPER_GOAL_FILE))
    parser.add_argument("--import-path", default=AGDA_IMPORT_PATH)

    model = parser.add_argument_group("model")
    model.add_argument("--model", default=DEFAULT_MODEL,
                       help="Ollama tag (qwen3.5:4b) or Claude id (claude-sonnet-5).")
    model.add_argument("--backend", default=DEFAULT_BACKEND,
                       choices=["auto", "ollama", "anthropic"])
    model.add_argument("--base-url", default=OLLAMA_BASE_URL)
    model.add_argument("--think", dest="think", action="store_true", default=None,
                       help="Ollama: enable the model's thinking mode.")
    model.add_argument("--no-think", dest="think", action="store_false",
                       help="Ollama: disable thinking (default from config).")
    model.add_argument("--effort", default=config.ANTHROPIC_EFFORT,
                       choices=["low", "medium", "high", "xhigh", "max"],
                       help="Anthropic: thinking effort.")
    model.add_argument("--llm-timeout", type=int, default=config.LLM_TIMEOUT_SECONDS)
    model.add_argument("--formalizer", default=None,
                       help="Ollama tag of the autoformalize fine-tune. With it, --model only "
                            "drafts; the formalizer writes lemma statements and sketches "
                            "(proof/formalizer.py). Implies --place-holes.")
    model.add_argument("--formalizer-url", default=OLLAMA_BASE_URL)

    problem = parser.add_argument_group("problem")
    problem.add_argument(
        "--informal-statement",
        default=None,
        help="Natural-language statement. Defaults to the Agda signature.",
    )
    problem.add_argument(
        "--informal-proof",
        default=None,
        help="Path to a human-written informal proof, skipping the draft stage.",
    )
    problem.add_argument(
        "--reference",
        default=None,
        help="Agda file (under --import-path) with a finished proof of the same "
             "declaration. Its decomposition is logged and compared with the run's.",
    )

    budget = parser.add_argument_group("budget")
    budget.add_argument("--draft-samples", type=int, default=DRAFT_SAMPLES)
    budget.add_argument("--sketch-max-attempts", type=int, default=SKETCH_MAX_ATTEMPTS)
    budget.add_argument("--gap-llm-attempts", type=int, default=GAP_LLM_ATTEMPTS)
    budget.add_argument("--max-depth", type=int, default=MAX_DEPTH)
    budget.add_argument("--mimer-timeout", type=int, default=MIMER_TIMEOUT_SECONDS)
    budget.add_argument("--no-mimer", action="store_true", help="Skip Agda's auto.")
    budget.add_argument("--place-holes", action="store_true",
                        help="When a sketch fails to check, place holes where it fails "
                             "instead of only asking again (proof/holes.py).")

    logging = parser.add_argument_group("logging")
    logging.add_argument("--runs-dir", default=str(RUNS_ROOT),
                         help="Where to write runs/<id>/{meta,events,summary}.")
    logging.add_argument("--tag", default="", help="Short label appended to the run id.")
    logging.add_argument("--no-log", action="store_true", help="Do not write a run directory.")
    logging.add_argument(
        "--no-isolate", action="store_true",
        help="Work on agda_files/ in place instead of a per-run copy under the run dir. "
             "Concurrent runs on the same tree corrupt each other; the copy also "
             "leaves the final Agda state in the run dir.",
    )
    logging.add_argument("--quiet", action="store_true")

    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)

    informal_proof_text = None

    if args.informal_proof:
        informal_proof_text = Path(args.informal_proof).read_text()

    think = config.OLLAMA_THINK if args.think is None else args.think

    backend = make_backend(
        model=args.model,
        backend=args.backend,
        base_url=args.base_url,
        think=think,
        effort=args.effort,
    )
    llm = ProofLLM(backend=backend, timeout=args.llm_timeout)

    if args.formalizer:
        llm = make_formalizer(llm, args.formalizer, args.formalizer_url, args.llm_timeout)
        args.place_holes = True

    run_config = {
        key: value for key, value in vars(args).items()
        if key not in {"runs_dir", "tag", "no_log", "quiet"}
    }
    run_config["think"] = think
    run_config["pipeline_defaults"] = {
        name: getattr(config, name)
        for name in dir(config)
        if name.isupper() and not name.startswith("_")
        and isinstance(getattr(config, name), (int, float, str, bool))
    }

    logger = None

    if not args.no_log:
        logger = RunLogger(
            root=Path(args.runs_dir),
            model=args.model,
            backend=getattr(backend, "name", args.backend),
            tag=args.tag,
            config=run_config,
            project_root=PROJECT_ROOT,
        )
        set_run_logger(logger)

        if not args.quiet:
            print(f"Logging to {logger.dir}")

    agda_file, helpers_file, helper_goal_file, reference_file, import_path = resolve_agda_paths(
        args, isolate_into=(None if (logger is None or args.no_isolate) else logger.dir),
    )
    reset_helpers_file(helpers_file)

    if logger is not None:
        logger.event(
            "run_start",
            file=str(agda_file),
            import_path=import_path,
            isolated=not args.no_isolate,
            source=agda_file.read_text(),
            argv=sys.argv[1:] if argv is None else argv,
        )

    started = time.monotonic()
    result: DSPResult | None = None
    error: BaseException | None = None

    try:
        result = prove_dsp(
            agda_file=agda_file,
            helpers_file=helpers_file,
            helper_goal_file=helper_goal_file,
            informal_statement=args.informal_statement,
            informal_proof_text=informal_proof_text,
            llm=llm,
            model=args.model,
            draft_samples=args.draft_samples,
            sketch_max_attempts=args.sketch_max_attempts,
            hammer=HammerConfig(
                use_mimer=not args.no_mimer,
                mimer_timeout=args.mimer_timeout,
                llm_attempts=args.gap_llm_attempts,
                import_path=import_path,
            ),
            max_depth=args.max_depth,
            history=ProofHistory(),
            verbose=not args.quiet,
            place_holes=args.place_holes,
        )

        if reference_file is not None:
            compare_with_reference(result, reference_file, import_path, quiet=args.quiet)
    except BaseException as exc:  # log it, then re-raise (incl. KeyboardInterrupt)
        error = exc
        raise
    finally:
        if logger is not None:
            logger.finish(
                result=result,
                success=bool(result and result.success),
                target=result.target_name if result else None,
                error=f"{type(error).__name__}: {error}" if error else None,
                llm_calls=llm.calls,
                wall_s=round(time.monotonic() - started, 3),
            )

            if result is not None and result.final_source:
                (logger.dir / "final_proof.agda").write_text(result.final_source)

                if helpers_file.exists():
                    (logger.dir / "final_helpers.agda").write_text(helpers_file.read_text())

                # The pipeline restores the target on exit. In an isolated copy
                # we want the run directory to hold the finished, checkable
                # tree instead, so put the proof back.
                if not args.no_isolate:
                    agda_file.write_text(result.final_source)

    assert result is not None
    report(result)

    if result.success and result.final_source:
        out_dir = PROJECT_ROOT / "proofs"
        out_dir.mkdir(exist_ok=True)
        out_path = out_dir / f"{result.target_name}.agda"
        out_path.write_text(result.final_source)
        print(f"\nProof written to {out_path}")

    if logger is not None:
        print(f"Run log: {logger.dir}")

    return 0 if result.success else 1


def make_formalizer(drafter: ProofLLM, model: str, base_url: str, timeout: int, path: str = ""):
    """The autoformalize fine-tune, on its raw prompt with its card's sampling."""

    backend = OllamaBackend(
        model=model, base_url=base_url, think=None, raw=True,
        temperature=0.6, top_p=0.95, num_predict=1024,
    )
    return FormalizerLLM(drafter=drafter, backend=backend, path=path, timeout=timeout)


def introduced_lemmas(result: DSPResult) -> set[str]:
    """Every lemma the run stated itself, at any depth (drafted or promoted)."""

    names = {lemma.name for lemma in result.sketch.lemmas} if result.sketch else set()
    names |= {
        r.method.split("lemma:", 1)[1].split(" :: ", 1)[0].strip()
        for r in result.gap_results if r.method.startswith("lemma:")
    }
    for sub in result.lemma_results:
        names |= {sub.target_name} | introduced_lemmas(sub)
    return names


def compare_with_reference(
    result: DSPResult, reference_file: Path, import_path: str, quiet: bool
) -> None:
    """
    Decompose the reference proof and line the run up against it: the
    finished proof if there is one, otherwise the last accepted sketch, so a
    failed run still shows where its decomposition parted ways.
    """

    reference = log_decomposition(
        reference_file, result.target_name, import_path, role="reference"
    )

    if reference is not None:
        compare_with_decomposition(result, reference, quiet)


def compare_with_decomposition(result: DSPResult, reference, quiet: bool = True):
    """Line the run's proof (or last sketch) up against a reference decomposition."""

    candidate, label = result.decomposition, "run proof"

    if candidate is None and result.sketch is not None:
        candidate, label = result.sketch.decomposition, "run sketch"

    if candidate is None:
        return None

    try:
        comparison = compare(candidate, reference, introduced=introduced_lemmas(result))
    except Exception as error:  # analysis only; never fail a finished run
        run_logger().event(
            "decomposition_compare", ok=False, error=f"{type(error).__name__}: {error}"
        )
        return None

    text = comparison.render(label, "reference")

    run_logger().event("decomposition_compare", comparison=comparison, text=text)

    if not quiet:
        print(f"\n{text}")

    return comparison


def resolve_agda_paths(
    args: argparse.Namespace, isolate_into: Path | None
) -> tuple[Path, Path, Path, Path | None, str]:
    """
    (target file, helpers file, helper-goal file, reference file or None,
    agda import path).

    With `isolate_into`, the whole Agda tree is copied under that directory and
    the paths are re-rooted there, so the repository copy is never touched and
    two runs cannot trample each other's Helpers.agda.
    """

    agda_file = Path(args.file).resolve()
    helpers_file = Path(args.helpers_file).resolve()
    helper_goal_file = Path(args.helper_goal_file).resolve()
    reference_file = Path(args.reference).resolve() if args.reference else None
    root = Path(args.import_path).resolve()

    if isolate_into is None:
        return agda_file, helpers_file, helper_goal_file, reference_file, str(root)

    for path in (agda_file, helpers_file, helper_goal_file, reference_file):
        if path is not None and root not in path.parents:
            print(f"warning: {path} is outside {root}; running without isolation")
            return agda_file, helpers_file, helper_goal_file, reference_file, str(root)

    copy_root = isolate_into / root.name
    shutil.copytree(
        root, copy_root,
        ignore=shutil.ignore_patterns("*.agdai", "_build"),
        dirs_exist_ok=True,
    )

    def rerooted(path: Path) -> Path:
        return copy_root / path.relative_to(root)

    return (
        rerooted(agda_file), rerooted(helpers_file), rerooted(helper_goal_file),
        rerooted(reference_file) if reference_file is not None else None,
        str(copy_root),
    )


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
    sys.exit(main())
