"""
Run DSP (proof/proof_sketch.py) on real library theorems and compare each
result's decomposition with the library's own proof.

    python cli/run_dsp_dataset.py SAMPLE.json \\
        --model qwen3.5:4b --base-url http://localhost:11435 \\
        --formalizer hf.co/astral-expmath/qwen3.5-4b-agda-autoformalize-context-GGUF:Q8_0 \\
        --formalizer-url http://localhost:11436 \\
        --agda-bin ~/agda/tools/agda-2.8.0/agda --tag library --limit 3

SAMPLE.json is a list of theorems from the datasets: repo, commit, include,
path, name, line, and the formalizer's `prompt` (its file, header, context and
the informal statement), as in agda-autoformalize-context.

Each theorem is proved in place in a mirror of its checkout (util.checkout):
the file is cut after the theorem and its proof replaced by a hole, and the
lemmas the run states live just above it (proof/layout.InFileLayout). `--model`
drafts; `--formalizer` (the autoformalize fine-tune) writes lemma statements
and sketches, and holes are placed where its proofs fail. Without
`--formalizer`, `--model` does every stage with the usual prompts.

The run writes runs/<id>/: meta.json and summary.json for the run,
results.jsonl with one record per theorem (the decomposition the run found:
draft, lemmas and how each was proved, holes and what closed them, and its
comparison with the library proof), and theorems/<NN>-<name>/ with each
theorem's own events.jsonl (every model call and Agda check) and its final
proof or best sketch as final.agda. `--jobs` proves theorems in parallel,
each in its own process and its own mirror of the checkout.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

from cli.run_dsp import compare_with_decomposition, make_formalizer
from core import config
from core.hammer import HammerConfig
from core.llm_client import ProofLLM, make_backend
from core.proof_history import ProofHistory
from core.proof_state import DSPResult
from core.run_log import RunLogger, set_run_logger
from proof.layout import InFileLayout
from proof.proof_sketch import prove_dsp
from util.agda_data import checkout_for
from util.checkout import mirrored
from util.deproof import decompose


# A library module with its imports can take minutes to load cold.
LIBRARY_AGDA_TIMEOUT = 900


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("sample", help="JSON list of theorems.")
    parser.add_argument("--model", default=config.DEFAULT_MODEL, help="Drafts (and, alone, everything).")
    parser.add_argument("--base-url", default=config.OLLAMA_BASE_URL)
    parser.add_argument("--formalizer", default=None, nargs="?", const=config.FORMALIZER_MODEL,
                        help="Ollama tag of the autoformalize fine-tune (bare flag: FORMALIZER_MODEL).")
    parser.add_argument("--formalizer-url", default=config.FORMALIZER_URL)
    parser.add_argument("--agda-bin", default=None)
    parser.add_argument("--library-file", default=str(config.AGDA_LIBRARY_FILE))
    parser.add_argument("--checkouts", default=str(config.CHECKOUTS_ROOT))
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--draft-samples", type=int, default=1)
    parser.add_argument("--sketch-max-attempts", type=int, default=2)
    parser.add_argument("--max-depth", type=int, default=2)
    parser.add_argument("--gap-llm-attempts", type=int, default=1,
                        help="Without --formalizer: model attempts per hole.")
    parser.add_argument("--no-mimer", action="store_true")
    parser.add_argument("--jobs", type=int, default=1, help="Theorems proved in parallel.")
    parser.add_argument("--no-draft", action="store_true",
                        help="Skip drafting: the formalizer writes the proof from the statement alone.")
    parser.add_argument("--max-lemmas", type=int, default=3,
                        help="With --formalizer: lemmas stated from the draft (0: the draft is only "
                             "shown as comments).")
    parser.add_argument("--tag", default="library")
    parser.add_argument("--runs-dir", default=str(config.RUNS_ROOT))
    args = parser.parse_args(argv)

    items = json.loads(Path(args.sample).read_text())[: args.limit]

    logger = RunLogger(
        root=Path(args.runs_dir), model=args.formalizer or args.model,
        backend="ollama", tag=args.tag,
        config=dict(vars(args)), project_root=config.PROJECT_ROOT,
    )
    set_run_logger(logger)
    results_path = logger.dir / "results.jsonl"
    print(f"Logging to {logger.dir}", file=sys.stderr)

    started = time.monotonic()
    jobs = [(index, item, vars(args), str(logger.dir)) for index, item in enumerate(items)]
    records: list[dict] = []

    def keep(record: dict) -> None:
        records.append(record)
        with results_path.open("a") as sink:
            sink.write(json.dumps(record, ensure_ascii=False, default=str) + "\n")
        print(_summary(record), file=sys.stderr, flush=True)

    try:
        if args.jobs <= 1:
            for job in jobs:
                keep(run_theorem(*job))
        else:
            with ProcessPoolExecutor(max_workers=args.jobs) as pool:
                for future in as_completed(pool.submit(run_theorem, *job) for job in jobs):
                    keep(future.result())
    finally:
        logger.finish(
            result=None, success=None, target=None, error=None,
            theorems=len(records), proved=sum(bool(r.get("success")) for r in records),
            wall_s=round(time.monotonic() - started, 1),
        )

    return 0


def run_theorem(index: int, item: dict, options: dict, run_dir: str) -> dict:
    """One theorem in its own logger (and, under --jobs, its own process)."""

    args = argparse.Namespace(**options)

    if args.agda_bin:
        config.AGDA_BIN = args.agda_bin

    config.AGDA_FLAGS = [
        "--no-default-libraries", f"--library-file={args.library_file}",
    ]

    drafter = ProofLLM(backend=make_backend(model=args.model, base_url=args.base_url, think=False))
    llm = drafter

    if args.formalizer:
        llm = make_formalizer(drafter, args.formalizer, args.formalizer_url, 600)
        llm.max_lemmas = args.max_lemmas

    theorem_dir = Path(run_dir) / "theorems"
    logger = RunLogger(
        root=theorem_dir, model=args.formalizer or args.model, backend="ollama",
        run_id=f"{index:02d}-{_slug(item['name'])}", config={"item": index, **options},
        project_root=config.PROJECT_ROOT,
    )
    set_run_logger(logger)

    try:
        record = run_item(item, args, llm)
    except Exception as error:   # one theorem must not end the run
        record = {"repo": item["repo"], "path": item["path"], "name": item["name"],
                  "stage": "error", "error": f"{type(error).__name__}: {error}"}
    finally:
        logger.finish(result=None, success=None, target=item["name"], error=None,
                      llm_calls=llm.calls + (drafter.calls if llm is not drafter else 0))

    record["index"] = index
    record["log"] = str(logger.dir)

    # The proof (or the best sketch) as a file, kept out of results.jsonl.
    final, sketch = record.pop("final_source_full", None), record.pop("sketch_source_full", None)
    if final:
        (logger.dir / "final.agda").write_text(final)
    elif sketch:
        (logger.dir / "sketch.agda").write_text(sketch)

    return record


def _slug(text: str) -> str:
    return "".join(c if c.isalnum() else "-" for c in text).strip("-")[:40] or "theorem"


def run_item(item: dict, args: argparse.Namespace, llm: ProofLLM) -> dict:
    """One theorem: reference decomposition, DSP in place, comparison."""

    record: dict = {"repo": item["repo"], "path": item["path"], "name": item["name"]}
    started = time.monotonic()
    root = checkout_for(item["repo"], item["commit"], Path(args.checkouts))
    prompt = item.get("prompt", "")
    informal = _tag(prompt, "informal") or None

    if hasattr(llm, "path"):
        llm.path = _tag(prompt, "file") or item["path"]

    with mirrored(root, item["path"]) as tree:
        agda_file = tree / item["path"]
        import_path = str(tree / item["include"].rstrip("/"))
        hammer = HammerConfig(
            tactics=("refl",),
            use_mimer=not args.no_mimer,
            llm_attempts=0 if args.formalizer else args.gap_llm_attempts,
            import_path=import_path,
            agda_timeout=LIBRARY_AGDA_TIMEOUT,
        )

        try:
            reference = decompose(agda_file, item["name"], import_path, line=item["line"],
                                  timeout=LIBRARY_AGDA_TIMEOUT)
            record["reference"] = reference.render()
        except Exception as error:
            reference = None
            record["reference_error"] = f"{type(error).__name__}: {error}"

        try:
            layout = InFileLayout(agda_file, item["name"], item["line"])
            result = prove_dsp(
                agda_file=agda_file,
                layout=layout,
                informal_statement=informal,
                llm=llm,
                draft_samples=args.draft_samples,
                sketch_max_attempts=args.sketch_max_attempts,
                hammer=hammer,
                max_depth=args.max_depth,
                history=ProofHistory(),
                verbose=False,
                place_holes=bool(args.formalizer),
                draft=not args.no_draft,
                target_name=item["name"],
            )
        except Exception as error:  # one theorem must not end the run
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


def _tag(prompt: str, name: str) -> str:
    match = re.search(rf"<{name}>\n?(.*?)</{name}>", prompt, re.DOTALL)
    return match.group(1).strip() if match else ""


def _summary(record: dict) -> str:
    def lemmas(r: dict, depth: int = 1) -> str:
        parts = []
        for sub in r.get("lemma_results", []):
            parts.append(f"{'ok' if sub['success'] else sub.get('stage') or 'fail'}"
                         + (f"({lemmas(sub, depth + 1)})" if sub.get("lemma_results") else ""))
        return ",".join(parts)

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
