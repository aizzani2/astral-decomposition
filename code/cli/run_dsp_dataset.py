"""
Run DSP (proof/proof_sketch.py) on a sample of library theorems and compare
each result's decomposition with the library's own proof.

    python cli/run_dsp_dataset.py SAMPLE.json --model claude-sonnet-5-5 \\
        --tag library --limit 3

SAMPLE.json is a list of theorems from the datasets (cli/sample_dataset.py):
repo, commit, include, path, name, line, and the agda-autoformalize-context
`prompt`, whose informal statement the run starts from. Each theorem is
proved as cli/run_dsp.py proves one, in a mirror of its checkout (which must
be at the pinned commit; see cli/doctor.py).

The run writes runs/<id>/: meta.json and summary.json for the run,
results.jsonl with one record per theorem, and theorems/<NN>-<name>/ with
each theorem's own events.jsonl and its final.agda (or best sketch.agda).
`--jobs` proves theorems in parallel, each in its own process and mirror.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

from cli.run_dsp import (
    add_run_options,
    backend_name,
    make_llm,
    prove_theorem,
    save_record,
    summary_line,
)
from core import config
from core.run_log import RunLogger, set_run_logger
from util.agda_data import checkout_for


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("sample", help="JSON list of theorems.")
    parser.add_argument("--checkouts", default=str(config.CHECKOUTS_ROOT))
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--jobs", type=int, default=1, help="Theorems proved in parallel.")
    add_run_options(parser, tag="library")
    args = parser.parse_args(argv)

    items = json.loads(Path(args.sample).read_text())[: args.limit]

    logger = RunLogger(
        root=Path(args.runs_dir), model=args.model, backend=backend_name(args.model),
        tag=args.tag, config=dict(vars(args)), project_root=config.PROJECT_ROOT,
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
        print(summary_line(record), file=sys.stderr, flush=True)

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
    llm = make_llm(args)

    logger = RunLogger(
        root=Path(run_dir) / "theorems", model=args.model, backend=backend_name(args.model),
        run_id=f"{index:02d}-{_slug(item['name'])}", config={"item": index, **options},
        project_root=config.PROJECT_ROOT,
    )
    set_run_logger(logger)

    try:
        root = checkout_for(item["repo"], item["commit"], Path(args.checkouts))
        informal = _tag(item.get("prompt", ""), "informal") or None
        record = prove_theorem(
            root, item["path"], item["include"], item["name"], item["line"], informal, args, llm,
        )
    except Exception as error:   # one theorem must not end the run
        record = {"path": item["path"], "name": item["name"],
                  "stage": "error", "error": f"{type(error).__name__}: {error}"}
    finally:
        logger.finish(result=None, success=None, target=item["name"], error=None,
                      llm_calls=llm.calls)

    record.update(repo=item["repo"], index=index, log=str(logger.dir))
    save_record(record, logger.dir)
    return record


def _slug(text: str) -> str:
    return "".join(c if c.isalnum() else "-" for c in text).strip("-")[:40] or "theorem"


def _tag(prompt: str, name: str) -> str:
    match = re.search(rf"<{name}>\n?(.*?)</{name}>", prompt, re.DOTALL)
    return match.group(1).strip() if match else ""


if __name__ == "__main__":
    raise SystemExit(main())
