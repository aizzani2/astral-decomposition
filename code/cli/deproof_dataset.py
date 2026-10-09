"""
Run deproof over the astral-expmath datasets: for each declaration with an
informal proof, take its formal proof apart and export sketches, writing one
JSON line per declaration.

    python cli/deproof_dataset.py \\
        --informal ~/agda/data/hf/agda-informalize-stdlib/data/train-00000-of-00001.parquet \\
        --decls    ~/agda/data/hf/agda-decls/data/train-00000-of-00001.parquet \\
        --agda-bin ~/agda/tools/agda-2.8.0/agda \\
        --path src/Data/Nat/Properties.agda --limit 20 --out deproof-nat.jsonl

Each line holds the dataset row (informal statement and proof, signature,
definition), the decomposition, and per granularity the sketch excerpt, its
hole goals, the lemmas it lifted, and whether Agda accepted it. The output is
appended to and rows already in it are skipped, so a run can be resumed.
Files are handled in parallel with --jobs; each job works in its own mirror of
the checkout, which is never written to.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import random
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

from core import config
from core.config import CHECKOUTS_ROOT
from util.agda_data import DatasetDecl, checkout_for, join_informal, load_rows
from util.checkout import mirrored
from util.deproof import decompose
from util.sketch_export import GRANULARITIES, export_sketch


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--informal", required=True, help="agda-informalize-* parquet file.")
    parser.add_argument("--decls", required=True, help="agda-decls parquet file (for ranges).")
    parser.add_argument("--out", required=True, help="JSONL output; appended to, resumable.")
    parser.add_argument("--checkouts", default=str(CHECKOUTS_ROOT),
                        help="Directory holding one checkout per source repo.")
    parser.add_argument("--agda-bin", default=None, help="Agda binary (default: $AGDA_BIN or agda).")
    parser.add_argument("--kinds", default="lemma,theorem",
                        help="Informal kinds to keep (comma-separated); '' keeps all.")
    parser.add_argument("--path", action="append", default=[],
                        help="Only declarations in files whose path contains this (repeatable).")
    parser.add_argument("--limit", type=int, default=None, help="At most this many declarations.")
    parser.add_argument("--sample", type=int, default=None,
                        help="A seeded random sample of this many declarations, across files.")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--granularity", action="append", choices=GRANULARITIES, default=[],
                        help="Sketch granularities to export (default: step and lemma).")
    parser.add_argument("--jobs", type=int, default=1, help="Files processed in parallel.")
    args = parser.parse_args(argv)

    granularities = args.granularity or ["step", "lemma"]
    kinds = {k for k in args.kinds.split(",") if k}

    decls = join_informal(load_rows(args.informal), load_rows(args.decls))
    decls = [
        d for d in decls
        if d.informal_proof
        and (not kinds or d.kind in kinds)
        and (not args.path or any(p in d.path for p in args.path))
    ]

    out = Path(args.out)
    done = set()

    if out.exists():
        for line in out.read_text().splitlines():
            if line.strip():
                done.add(json.loads(line)["id"])

    todo = [d for d in decls if d.id not in done]

    if args.sample is not None:
        todo = random.Random(args.seed).sample(todo, min(args.sample, len(todo)))

    todo = todo[: args.limit]
    print(f"{len(decls)} declarations selected, {len(done)} already done, {len(todo)} to do",
          file=sys.stderr)

    by_file: dict[tuple[str, str, str], list[DatasetDecl]] = {}
    for d in todo:
        by_file.setdefault((d.repo, d.commit, d.path), []).append(d)

    jobs = [
        (decls_in_file, args.checkouts, args.agda_bin, granularities)
        for decls_in_file in by_file.values()
    ]

    with out.open("a") as sink:
        def write(records: list[dict]) -> None:
            for record in records:
                sink.write(json.dumps(record, ensure_ascii=False, default=str) + "\n")
                print(_summary(record), file=sys.stderr, flush=True)
            sink.flush()

        if args.jobs <= 1:
            for job in jobs:
                write(_run_file(*job))
        else:
            with ProcessPoolExecutor(max_workers=args.jobs) as pool:
                for future in as_completed(pool.submit(_run_file, *job) for job in jobs):
                    write(future.result())

    return 0


def _run_file(
    decls: list[DatasetDecl], checkouts: str, agda_bin: str | None, granularities: list[str]
) -> list[dict]:
    """Every declaration of one file, in one mirror of its checkout."""

    if agda_bin:
        config.AGDA_BIN = agda_bin

    # A checkout says what it needs in its own .agda-lib; the user's default
    # libraries are for whatever Agda installed them.
    if "--no-default-libraries" not in config.AGDA_FLAGS:
        config.AGDA_FLAGS = [*config.AGDA_FLAGS, "--no-default-libraries"]

    first = decls[0]
    records: list[dict] = []

    try:
        root = checkout_for(first.repo, first.commit, Path(checkouts))
    except (FileNotFoundError, ValueError) as error:
        return [_record(d, error=str(error)) for d in decls]

    with mirrored(root, first.path) as tree:
        agda_file = tree / first.path
        import_path = str(tree / first.include)

        for decl in decls:
            started = time.monotonic()

            try:
                decomposition = decompose(agda_file, decl.name, import_path, line=decl.line)
                sketches = {
                    granularity: export_sketch(
                        agda_file, decl.name, granularity, import_path,
                        decomposition=decomposition, line=decl.line,
                    )
                    for granularity in granularities
                }
            except Exception as error:  # one bad declaration must not end the file
                records.append(_record(
                    decl, error=f"{type(error).__name__}: {error}",
                    seconds=time.monotonic() - started,
                ))
                continue

            records.append(_record(
                decl,
                decomposition=dataclasses.asdict(decomposition),
                rendered=decomposition.render(),
                sketches={
                    granularity: {
                        "valid": sketch.valid,
                        "excerpt": sketch.excerpt,
                        "holes": sketch.holes,
                        "lemmas": sketch.lemmas,
                        "problems": sketch.problems,
                        "warnings": sketch.warnings,
                        "notes": sketch.notes,
                    }
                    for granularity, sketch in sketches.items()
                },
                seconds=time.monotonic() - started,
            ))

    return records


def _record(decl: DatasetDecl, seconds: float = 0.0, **fields) -> dict:
    return {
        "id": decl.id,
        **dataclasses.asdict(decl),
        **fields,
        "seconds": round(seconds, 1),
    }


def _summary(record: dict) -> str:
    if record.get("error"):
        return f"{record['name']:<30} ERROR {record['error'][:150]}"

    decomposition = record["decomposition"]
    n_steps = sum(len(c["steps"]) for c in decomposition["clauses"])
    parts = [
        f"{g}={'BAD' if not s['valid'] else 'warn' if s['warnings'] else 'ok'}({len(s['holes'])} holes"
        f"{', ' + str(len(s['lemmas'])) + ' lemmas' if s['lemmas'] else ''})"
        for g, s in record["sketches"].items()
    ]

    return (
        f"{record['name']:<30} {record['seconds']:>5}s "
        f"{len(decomposition['clauses'])} clauses {n_steps} steps  " + "  ".join(parts)
    )


if __name__ == "__main__":
    raise SystemExit(main())
