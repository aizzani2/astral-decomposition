"""
Summarise the run logs written by run_dsp.py.

    python cli/analyze_runs.py                 # one row per run
    python cli/analyze_runs.py --llm RUN_ID    # every model call in one run
    python cli/analyze_runs.py --events RUN_ID # every event (kind, scope, key fields)
    python cli/analyze_runs.py --dataset RUN_ID # a run_dsp_dataset.py run: per theorem, the
                                               # lemma funnel, holes, repairs, comparison
    python cli/analyze_runs.py --decomposition RUN_ID
                                               # each finished proof taken apart, and
                                               # the comparison with --reference
    python cli/analyze_runs.py --json          # machine-readable table

RUN_ID may be a prefix or any unique substring of the run directory name.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
import sys
from pathlib import Path
from typing import Any

from core.config import RUNS_ROOT
from util.deproof import Decomposition, compare


def load_runs(root: Path) -> list[dict[str, Any]]:
    runs: list[dict[str, Any]] = []

    for run_dir in sorted(p for p in root.iterdir() if p.is_dir()):
        meta_path = run_dir / "meta.json"
        summary_path = run_dir / "summary.json"

        if not meta_path.exists():
            continue

        meta = json.loads(meta_path.read_text())
        summary = json.loads(summary_path.read_text()) if summary_path.exists() else {}
        events = read_events(run_dir)

        runs.append(summarise(run_dir, meta, summary, events))

    return runs


def read_events(run_dir: Path) -> list[dict[str, Any]]:
    path = run_dir / "events.jsonl"

    if not path.exists():
        return []

    events: list[dict[str, Any]] = []

    for line in path.read_text().splitlines():
        line = line.strip()

        if not line:
            continue

        try:
            events.append(json.loads(line))
        except json.JSONDecodeError:
            continue

    return events


def failure_stage(result: dict[str, Any] | None, events: list[dict[str, Any]]) -> str:
    if result is None:
        return "crashed/unfinished"

    if result.get("success"):
        return "-"

    # The last top-level dsp_result event knows which stage gave up.
    for event in reversed(events):
        if event.get("kind") == "dsp_result" and event.get("depth", 0) == 0:
            stage = event.get("stage", "?")

            if stage == "lemma":
                failed = [r for r in result.get("lemma_results", []) if not r.get("success")]
                if failed:
                    return f"lemma:{failed[-1].get('target_name')}"

            return stage

    return "?"


def summarise(
    run_dir: Path,
    meta: dict[str, Any],
    summary: dict[str, Any],
    events: list[dict[str, Any]],
) -> dict[str, Any]:
    result = summary.get("result")
    llm_calls = [e for e in events if e.get("kind") == "llm_call"]
    by_stage: dict[str, int] = {}

    for call in llm_calls:
        by_stage[call.get("stage", "?")] = by_stage.get(call.get("stage", "?"), 0) + 1

    gap_results = [e for e in events if e.get("kind") == "gap_result"]
    methods: dict[str, int] = {}

    for gap in gap_results:
        if gap.get("success"):
            method = gap.get("method", "?").split(":", 1)[0]
            methods[method] = methods.get(method, 0) + 1

    sketch_attempts = [e for e in events if e.get("kind") == "sketch_attempt"]

    return {
        "run_id": run_dir.name,
        "model": meta.get("model"),
        "backend": meta.get("backend"),
        "think": meta.get("config", {}).get("think"),
        "tag": meta.get("tag", ""),
        "git": meta.get("git_commit"),
        "target": summary.get("target") or (result or {}).get("target_name"),
        "success": summary.get("success"),
        "finished": bool(summary),
        "elapsed_s": summary.get("elapsed_s"),
        "llm_calls": len(llm_calls),
        "llm_by_stage": by_stage,
        "llm_errors": sum(1 for c in llm_calls if c.get("error")),
        "prompt_tokens": summary.get("token_totals", {}).get("prompt_tokens"),
        "output_tokens": summary.get("token_totals", {}).get("output_tokens"),
        "agda_checks": sum(1 for e in events if e.get("kind") == "agda_check"),
        "sketch_attempts": len(sketch_attempts),
        "sketch_accepted": sum(1 for e in sketch_attempts if e.get("accepted")),
        "gaps": len(gap_results),
        "gaps_closed": sum(1 for g in gap_results if g.get("success")),
        "gap_methods": methods,
        "failure_stage": failure_stage(result, events),
        "error": summary.get("error"),
    }


def print_table(rows: list[dict[str, Any]]) -> None:
    if not rows:
        print("No runs found.")
        return

    columns = [
        ("run_id", 38), ("model", 16), ("think", 5), ("target", 14), ("success", 7),
        ("elapsed_s", 9), ("llm_calls", 5), ("output_tokens", 8),
        ("sketch_attempts", 6), ("gaps_closed", 5), ("gaps", 4),
        ("gap_methods", 22), ("failure_stage", 22),
    ]
    header = {
        "llm_calls": "llm", "output_tokens": "out_tok", "sketch_attempts": "sketch",
        "gaps_closed": "closed", "elapsed_s": "elapsed",
    }

    def cell(row: dict[str, Any], key: str, width: int) -> str:
        value = row.get(key)

        if isinstance(value, dict):
            value = ",".join(f"{k}={v}" for k, v in value.items()) or "-"
        elif isinstance(value, float):
            value = f"{value:.0f}"
        elif value is None:
            value = "-"

        text = str(value)
        return (text[: width - 1] + "…") if len(text) > width else text.ljust(width)

    print(" ".join(header.get(k, k).ljust(w)[:w] for k, w in columns))
    print(" ".join("-" * w for _, w in columns))

    for row in rows:
        print(" ".join(cell(row, k, w) for k, w in columns))


def find_run(root: Path, needle: str) -> Path:
    matches = [p for p in root.iterdir() if p.is_dir() and needle in p.name]

    if len(matches) != 1:
        names = ", ".join(p.name for p in matches) or "none"
        raise SystemExit(f"Expected exactly one run matching {needle!r}, got: {names}")

    return matches[0]


def print_llm_calls(run_dir: Path, full: bool) -> None:
    for event in read_events(run_dir):
        if event.get("kind") != "llm_call":
            continue

        scope = f"d{event.get('depth', 0)}"

        if "draft_index" in event:
            scope += f"/draft{event['draft_index']}"

        head = (
            f"[{event['seq']:>4}] t={event['t']:>7.1f}s {scope:<10} "
            f"{event.get('stage', '?'):<16} {event.get('target', '?'):<14} "
            f"{event.get('duration_s', 0):>6.1f}s "
            f"in={event.get('prompt_tokens')} out={event.get('output_tokens')} "
            f"stop={event.get('stop_reason', '')}"
        )
        print(head)

        if event.get("error"):
            print(f"       ERROR: {event['error']}")

        text = event.get("text", "") or ""
        thinking = event.get("thinking", "") or ""

        if full:
            print("       --- prompt ---")
            print(indent(event.get("prompt", "")))
            if thinking:
                print("       --- thinking ---")
                print(indent(thinking))
            print("       --- response ---")
            print(indent(text))
        else:
            first = next((l for l in text.splitlines() if l.strip()), "")
            print(f"       {first[:110]}" + (f"  (+{len(thinking)} chars thinking)" if thinking else ""))


def print_events(run_dir: Path) -> None:
    skip = {"prompt", "text", "thinking", "source", "raw", "trial_source", "final_source",
            "helpers_source", "extra", "sketch", "context", "gaps", "steps",
            "decomposition", "comparison"}

    for event in read_events(run_dir):
        fields = {
            k: v for k, v in event.items()
            if k not in skip and k not in {"seq", "ts", "t", "kind"}
        }
        summary = json.dumps(fields, ensure_ascii=False, default=str)
        print(f"[{event['seq']:>4}] t={event['t']:>7.1f}s {event['kind']:<16} {summary[:200]}")


def print_decompositions(run_dir: Path) -> None:
    events = read_events(run_dir)
    found = False

    for event in events:
        if event.get("kind") not in ("decomposition", "decomposition_compare"):
            continue

        found = True
        label = (
            "comparison" if event["kind"] == "decomposition_compare"
            else f"{event.get('role', 'proof')} of {event.get('name') or event.get('target', '?')} "
                 f"(depth {event.get('depth', 0)})"
        )
        print(f"[{event['seq']:>4}] {label}")
        print(indent(event.get("text") or f"error: {event.get('error')}"))
        print()

    if not found:
        print("No decomposition events (runs before util/deproof, or nothing was proved).")
        return

    print_reference_comparisons(events)


def print_reference_comparisons(events: list[dict[str, Any]]) -> None:
    """
    Line every top-level sketch and proof up against the reference, not just
    the run's last one: a failed run may have tried the right split earlier.
    """

    logged = [
        e for e in events
        if e.get("kind") == "decomposition" and e.get("ok") and e.get("decomposition")
    ]
    reference = next((e for e in logged if e.get("role") == "reference"), None)

    if reference is None:
        return

    ref = Decomposition.from_dict(reference["decomposition"])
    print("Against the reference:")

    for event in logged:
        if event is reference or event.get("depth", 0) != 0 or event.get("name") != ref.name:
            continue

        label = f"{event.get('role')} (draft {event.get('draft_index', '?')})"
        comparison = compare(Decomposition.from_dict(event["decomposition"]), ref)
        print(f"[{event['seq']:>4}] {label}")
        print(indent(comparison.render(label, "reference")))
        print()


def dataset_events(run_dir: Path, rows: list[dict[str, Any]]) -> list[list[dict[str, Any]]]:
    """
    Each theorem's events, in results order. New runs keep them per theorem
    (theorems/<NN>-<name>/events.jsonl); older ones in one file, where a
    theorem starts when the depth-0 target changes.
    """

    by_index = {r.get("index", i): i for i, r in enumerate(rows)}
    out: list[list[dict[str, Any]]] = [[] for _ in rows]
    per_theorem = sorted((run_dir / "theorems").glob("*/events.jsonl")) if (run_dir / "theorems").is_dir() else []

    if per_theorem:
        for path in per_theorem:
            index = int(path.parent.name.split("-", 1)[0])
            if index in by_index:
                out[by_index[index]] = read_events(path.parent)
        return out

    started = [i for i, r in enumerate(rows) if r.get("stage") not in ("setup", "", None)]
    position, last = -1, None
    for event in read_events(run_dir):
        if event.get("depth") == 0 and event.get("target") and event["target"] != last:
            last, position = event["target"], position + 1
        if 0 <= position < len(started):
            out[started[position]].append(event)
    return out


def summarize_theorem(events: list[dict[str, Any]]) -> Counter:
    c: Counter = Counter()
    for e in events:
        k = e["kind"]
        if k == "llm_call":
            c[f"model s: {e.get('stage')}"] += e.get("duration_s") or 0
        elif k == "draft" and e.get("ok"):
            c["drafts"] += 1
            c["lemma steps drafted"] += e.get("n_lemma_steps") or 0
        elif k == "sketch_attempt":
            c["sketch attempts"] += 1
            if e.get("accepted"):
                c["sketches accepted"] += 1
                c["lemma statements kept"] += len(e.get("lemmas") or [])
        elif k == "sketch_repair":
            for r in e.get("repairs") or []:
                kind = ("lemma dropped" if r.startswith("dropped lemma") else
                        "binders introduced" if r.startswith("introduced") else
                        "chain holed" if r.startswith("chain") else
                        "clause holed" if r.startswith("clause") else "subterm holed")
                c[f"repair: {kind}"] += 1
        elif k == "gap_result":
            method = (e.get("method") or "").split(":")[0]
            method = "mimer" if method.startswith("mimer") else method
            c[f"hole: {method}"] += 1
        elif k == "promote":
            c["promotions tried"] += 1
            c["promotions stated"] += bool(e.get("ok"))
        elif k == "lemma_unused":
            c["lemmas unused"] += len(e.get("lemmas") or [])
        elif k == "lemma_end":
            c["lemmas tried"] += 1
            c["lemmas proved"] += bool(e.get("success"))
    return c


def print_dataset(run_dir: Path) -> None:
    rows = [json.loads(l) for l in (run_dir / "results.jsonl").read_text().splitlines() if l.strip()]
    events = dataset_events(run_dir, rows)
    total: Counter = Counter()

    print(f"{'library':10} {'theorem':26} {'result':12} {'sketch':>6} {'lemmas':>7} {'used':>4} "
          f"{'proved':>6} {'holes':>5} {'closed':>6} {'split':7} {'found':>5}")

    for row, evs in zip(rows, events):
        c = summarize_theorem(evs)
        total.update(c)
        holes = sum(v for k, v in c.items() if k.startswith("hole: "))
        closed = holes - c["hole: failed"]
        library = row["repo"].split("/")[-1].replace("agda-", "")
        result = "PROVED" if row.get("success") else row.get("stage", "?")
        split = {True: "same", False: "differs"}.get(row.get("same_split"), "-")
        print(f"{library:10} {row['name'][:26]:26} {result:12} "
              f"{c['sketches accepted']:>2}/{c['sketch attempts']:<3} {c['lemma statements kept']:>3}/{c['lemma steps drafted']:<3} "
              f"{c['lemmas tried']:>4} {c['lemmas proved']:>6} {holes:>5} {closed:>6} {split:7} "
              f"{len(row.get('lemma_pairs') or []):>5}")
        total["theorems"] += 1
        total["proved"] += bool(row.get("success"))
        total["same case split"] += row.get("same_split") is True
        total["lemmas the run found in the library proof"] += len(row.get("lemma_pairs") or [])

    print()
    order = ["theorems", "proved", "drafts", "lemma steps drafted", "lemma statements kept",
             "lemmas unused", "lemmas tried", "lemmas proved", "promotions tried", "promotions stated",
             "sketch attempts", "sketches accepted", "same case split",
             "lemmas the run found in the library proof"]
    for key in order + sorted(k for k in total if k not in order and not k.startswith("model s")):
        if key in total:
            print(f"  {total[key]:>6}  {key}")
    model = {k[len('model s: '):]: round(v / 60, 1) for k, v in total.items() if k.startswith("model s")}
    print(f"\nmodel minutes by stage: {model}")
    print(f"wall minutes: {sum(r.get('seconds', 0) for r in rows) / 60:.1f}")


def indent(text: str, prefix: str = "       | ") -> str:
    return "\n".join(prefix + line for line in text.splitlines())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--runs-dir", default=str(RUNS_ROOT))
    parser.add_argument("--json", action="store_true", help="Print the table as JSON.")
    parser.add_argument("--llm", metavar="RUN_ID", help="List every model call in one run.")
    parser.add_argument("--full", action="store_true", help="With --llm: print prompts and responses.")
    parser.add_argument("--events", metavar="RUN_ID", help="List every event in one run.")
    parser.add_argument("--dataset", metavar="RUN_ID",
                        help="Summarise a run_dsp_dataset.py run.")
    parser.add_argument("--decomposition", metavar="RUN_ID",
                        help="Show how each finished proof decomposes into steps and lemmas.")
    args = parser.parse_args(argv)

    root = Path(args.runs_dir)

    if not root.exists():
        print(f"No runs directory at {root}")
        return 1

    if args.llm:
        print_llm_calls(find_run(root, args.llm), full=args.full)
        return 0

    if args.events:
        print_events(find_run(root, args.events))
        return 0

    if args.dataset:
        print_dataset(find_run(root, args.dataset))
        return 0

    if args.decomposition:
        print_decompositions(find_run(root, args.decomposition))
        return 0

    rows = load_runs(root)

    if args.json:
        print(json.dumps(rows, indent=2, default=str))
    else:
        print_table(rows)

    return 0


if __name__ == "__main__":
    sys.exit(main())
