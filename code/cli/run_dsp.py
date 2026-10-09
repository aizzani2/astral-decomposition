"""
Run DSP (proof/proof_sketch.py) on one theorem of an Agda project.

    python cli/run_dsp.py ~/agda/data/agda-stdlib/src/Data/Nat/Properties.agda +-comm \\
        --model claude-sonnet-5-5 [--line N] [--informal "..."]

The project is the nearest directory above FILE with an .agda-lib. The run
works in a symlink mirror of it (util/checkout.py), so the project itself is
never written to. The library's own proof of NAME is taken apart first
(util/deproof.py), and the run's decomposition is compared with it.

The run writes runs/<id>/: meta.json, events.jsonl (every model call and
Agda check), summary.json, result.json (the decomposition the run found:
draft, lemmas and how each was proved, holes and what closed them, and its
comparison with the library's proof), and final.agda or the best
sketch.agda. cli/run_dsp_dataset.py runs the same thing over a sample.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

from core import config
from core.hammer import HammerConfig
from core.llm_client import ProofLLM, make_backend
from core.proof_history import ProofHistory
from core.proof_state import DSPResult
from core.run_log import RunLogger, run_logger, set_run_logger
from proof.proof_sketch import prove_dsp
from util.checkout import mirrored
from util.deproof import compare, decompose


# A library module with its imports can take minutes to load cold.
LIBRARY_AGDA_TIMEOUT = 900


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("file", help="An .agda file inside an Agda project.")
    parser.add_argument("name", help="The declaration to prove.")
    parser.add_argument("--line", type=int, default=None,
                        help="Line of its signature, when the name occurs more than once.")
    parser.add_argument("--informal", default=None,
                        help="Informal statement (default: the Agda signature).")
    add_run_options(parser, tag="")
    args = parser.parse_args(argv)

    agda_file = Path(args.file).resolve()
    root, include = project_of(agda_file)

    logger = RunLogger(
        root=Path(args.runs_dir), model=args.model, backend=backend_name(args.model),
        tag=args.tag, config=dict(vars(args)), project_root=config.PROJECT_ROOT,
    )
    set_run_logger(logger)
    print(f"Logging to {logger.dir}", file=sys.stderr)

    llm = make_llm(args)
    record: dict = {}

    try:
        record = prove_theorem(
            root, agda_file.relative_to(root), include, args.name, args.line,
            args.informal, args, llm, verbose=not args.quiet,
        )
    finally:
        logger.finish(result=None, success=bool(record.get("success")), target=args.name,
                      error=record.get("error"), llm_calls=llm.calls)

    save_record(record, logger.dir)
    (logger.dir / "result.json").write_text(json.dumps(record, ensure_ascii=False, indent=1, default=str))
    print(summary_line(record))

    if record.get("comparison"):
        print(f"\n{record['comparison']}")

    return 0 if record.get("success") else 1


# ---------------------------------------------------------------------------
# Shared with cli/run_dsp_dataset.py
# ---------------------------------------------------------------------------

def add_run_options(parser: argparse.ArgumentParser, tag: str) -> None:
    """The model, budget and logging options of a run."""

    parser.add_argument("--model", default=config.DEFAULT_MODEL,
                        help="Ollama tag (qwen3.5:4b) or Claude id (claude-sonnet-5-5).")
    parser.add_argument("--base-url", default=config.OLLAMA_BASE_URL, help="Ollama server.")
    parser.add_argument("--effort", default=config.ANTHROPIC_EFFORT,
                        choices=["low", "medium", "high", "xhigh", "max"], help="For a Claude model.")
    parser.add_argument("--llm-timeout", type=int, default=config.LLM_TIMEOUT_SECONDS)
    parser.add_argument("--draft-samples", type=int, default=1)
    parser.add_argument("--no-draft", action="store_true",
                        help="Skip drafting: the sketch is written from the statement alone.")
    parser.add_argument("--sketch-max-attempts", type=int, default=2)
    parser.add_argument("--max-depth", type=int, default=2)
    parser.add_argument("--gap-llm-attempts", type=int, default=1, help="Model attempts per hole.")
    parser.add_argument("--no-mimer", action="store_true")
    parser.add_argument("--place-holes", action="store_true",
                        help="Place holes where a sketch fails instead of rejecting it.")
    parser.add_argument("--tag", default=tag)
    parser.add_argument("--runs-dir", default=str(config.RUNS_ROOT))
    parser.add_argument("--quiet", action="store_true")


def make_llm(args: argparse.Namespace) -> ProofLLM:
    backend = make_backend(model=args.model, base_url=args.base_url, think=False, effort=args.effort)
    return ProofLLM(backend=backend, timeout=args.llm_timeout)


def backend_name(model: str) -> str:
    return "anthropic" if model.startswith("claude") else "ollama"


def project_of(agda_file: Path) -> tuple[Path, str]:
    """The project holding `agda_file` (nearest .agda-lib above it) and its include directory."""

    for directory in agda_file.parents:
        libs = sorted(directory.glob("*.agda-lib"))
        if libs:
            for line in libs[0].read_text().splitlines():
                if line.strip().startswith("include:"):
                    return directory, line.split(":", 1)[1].split()[0].rstrip("/")
            return directory, "."

    raise ValueError(f"No .agda-lib above {agda_file}: it is not in an Agda project.")


def prove_theorem(
    root: Path,
    path: Path | str,
    include: str,
    name: str,
    line: int | None,
    informal: str | None,
    args: argparse.Namespace,
    llm: ProofLLM,
    verbose: bool = False,
) -> dict:
    """
    Prove `name` in `root/path` in a mirror of the project: the library's own
    proof taken apart, the DSP run, and the two compared. Returns the record.
    """

    record: dict = {"path": str(path), "name": name}
    started = time.monotonic()

    with mirrored(root, path) as tree:
        agda_file = tree / path
        import_path = str(tree / include.rstrip("/"))
        hammer = HammerConfig(
            tactics=("refl",),
            use_mimer=not args.no_mimer,
            llm_attempts=args.gap_llm_attempts,
            import_path=import_path,
            agda_timeout=LIBRARY_AGDA_TIMEOUT,
        )

        try:
            reference = decompose(agda_file, name, import_path, line=line, timeout=LIBRARY_AGDA_TIMEOUT)
            record["reference"] = reference.render()
        except Exception as error:
            reference = None
            record["reference_error"] = f"{type(error).__name__}: {error}"

        try:
            result = prove_dsp(
                agda_file, name, line,
                informal_statement=informal,
                llm=llm,
                draft_samples=args.draft_samples,
                sketch_max_attempts=args.sketch_max_attempts,
                hammer=hammer,
                max_depth=args.max_depth,
                history=ProofHistory(),
                verbose=verbose,
                place_holes=args.place_holes,
                draft=not args.no_draft,
            )
        except Exception as error:  # one theorem must not end a dataset run
            record.update(stage="error", error=f"{type(error).__name__}: {error}")
            record["seconds"] = round(time.monotonic() - started, 1)
            return record

        record.update(summarize(result))

        if reference is not None:
            comparison = compare_with_decomposition(result, reference)
            if comparison is not None:
                record["comparison"] = comparison.render("run", "library")
                record["same_split"] = comparison.same_split
                record["lemma_pairs"] = comparison.lemma_pairs

    record["seconds"] = round(time.monotonic() - started, 1)
    return record


def save_record(record: dict, directory: Path) -> None:
    """The proof (or the best sketch) as a file, kept out of the record."""

    final, sketch = record.pop("final_source_full", None), record.pop("sketch_source_full", None)
    if final:
        (directory / "final.agda").write_text(final)
    elif sketch:
        (directory / "sketch.agda").write_text(sketch)


def summarize(result: DSPResult) -> dict:
    """The decomposition a DSP result found, compactly, recursing into its lemmas."""

    sketch = result.sketch

    return {
        "target": result.target_name,
        "success": result.success,
        "stage": result.stage,
        "draft": result.informal.as_numbered_text() if result.informal else None,
        "lemmas": [f"{l.name} : {l.signature}" for l in sketch.lemmas] if sketch else [],
        "sketch": sketch.raw_response[-3000:] if sketch else None,
        "holes": [
            {"goal": r.gap.goal_type, "closed": r.success, "method": r.method,
             "solution": r.solution}
            for r in result.gap_results
        ],
        "lemma_results": [summarize(r) for r in result.lemma_results],
        "decomposition": result.decomposition.render() if result.decomposition else None,
        "final_source_tail": (result.final_source or "")[-4000:] or None,
        "final_source_full": result.final_source,
        "sketch_source_full": sketch.source if sketch else None,
        "output": (result.output or "")[-1500:],
    }


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


def compare_with_decomposition(result: DSPResult, reference):
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

    run_logger().event(
        "decomposition_compare", comparison=comparison, text=comparison.render(label, "reference"),
    )

    return comparison


def summary_line(record: dict) -> str:
    def lemmas(r: dict) -> str:
        return ",".join(
            f"{'ok' if sub['success'] else sub.get('stage') or 'fail'}"
            + (f"({lemmas(sub)})" if sub.get("lemma_results") else "")
            for sub in r.get("lemma_results", [])
        )

    holes = record.get("holes", [])
    methods = ",".join(sorted({h["method"].split(":")[0] for h in holes})) or "-"
    split = {True: "split=same", False: "split=differs"}.get(record.get("same_split"), "")
    tail = record.get("error") or ""

    return (
        f"{record['name'][:28]:<28} {record.get('seconds', 0):>6}s "
        f"{'PROVED' if record.get('success') else record.get('stage', '?'):<11} "
        f"lemmas={len(record.get('lemmas', []))}[{lemmas(record)}] "
        f"holes={len(holes)}({methods}) {split} {tail[:100]}"
    )


if __name__ == "__main__":
    raise SystemExit(main())
