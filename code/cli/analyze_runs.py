"""
Summarise the run logs written by run_dsp.py.

    python cli/analyze_runs.py                 # one row per run
    python cli/analyze_runs.py --llm RUN_ID    # every model call in one run
    python cli/analyze_runs.py --events RUN_ID # every event (kind, scope, key fields)
    python cli/analyze_runs.py --json          # machine-readable table

RUN_ID may be a prefix or any unique substring of the run directory name.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from core.config import RUNS_ROOT


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
            "helpers_source", "extra", "sketch", "context", "gaps", "steps"}

    for event in read_events(run_dir):
        fields = {
            k: v for k, v in event.items()
            if k not in skip and k not in {"seq", "ts", "t", "kind"}
        }
        summary = json.dumps(fields, ensure_ascii=False, default=str)
        print(f"[{event['seq']:>4}] t={event['t']:>7.1f}s {event['kind']:<16} {summary[:200]}")


def indent(text: str, prefix: str = "       | ") -> str:
    return "\n".join(prefix + line for line in text.splitlines())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--runs-dir", default=str(RUNS_ROOT))
    parser.add_argument("--json", action="store_true", help="Print the table as JSON.")
    parser.add_argument("--llm", metavar="RUN_ID", help="List every model call in one run.")
    parser.add_argument("--full", action="store_true", help="With --llm: print prompts and responses.")
    parser.add_argument("--events", metavar="RUN_ID", help="List every event in one run.")
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

    rows = load_runs(root)

    if args.json:
        print(json.dumps(rows, indent=2, default=str))
    else:
        print_table(rows)

    return 0


if __name__ == "__main__":
    sys.exit(main())
