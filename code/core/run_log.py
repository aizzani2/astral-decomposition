"""
Structured run logging for the Draft / Sketch / Prove pipeline.

One run = one directory under `runs/`:

    runs/<timestamp>_<model>[_<tag>]/
        meta.json       who/what/when: model, backend, config, git commit, agda version
        events.jsonl    one JSON object per line, in order, for everything that happened
        summary.json    the final DSPResult plus aggregate counters (written at the end)

Every event carries: `seq`, `ts` (ISO-8601), `t` (seconds since run start), `kind`,
and whatever scope is active (target name, recursion depth, draft index, ...).
Scopes are pushed with `logger.scope(...)` so the stages don't have to thread
bookkeeping through every call.

Event kinds emitted by the pipeline (see the callers for exact fields):

    run_start / run_end          whole run
    llm_call                     every model call: stage, prompt, text, thinking,
                                 tokens, duration, error
    agda_check                   every Agda invocation: mode, source, result, duration
    draft                        one parsed informal proof (or a parse failure)
    sketch_attempt               one sketch candidate and whether Agda accepted it
    gap_start / gap_candidate / gap_result
                                 one hole; every term tried against it; the outcome
    lemma_start / lemma_end      one lemma obligation discharged recursively
    dsp_result                   result of one (possibly nested) DSP attempt

Access the active logger via `run_logger()`. When no run is active this returns a
no-op logger so library code never has to check.
"""

from __future__ import annotations

import dataclasses
import json
import os
import platform
import subprocess
import time
from collections import Counter
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterator


def _jsonable(value: Any) -> Any:
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        return dataclasses.asdict(value)

    if isinstance(value, Path):
        return str(value)

    if isinstance(value, (set, frozenset, tuple)):
        return list(value)

    return str(value)


def _slug(text: str) -> str:
    return "".join(c if c.isalnum() else "-" for c in text).strip("-")[:40]


def _git_commit(root: Path) -> str | None:
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=root, capture_output=True, text=True, timeout=5,
        )
        return out.stdout.strip() or None
    except Exception:
        return None


def _git_dirty(root: Path) -> bool | None:
    try:
        out = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=root, capture_output=True, text=True, timeout=5,
        )
        return bool(out.stdout.strip())
    except Exception:
        return None


def _agda_version() -> str | None:
    try:
        out = subprocess.run(["agda", "--version"], capture_output=True, text=True, timeout=5)
        return out.stdout.strip() or None
    except Exception:
        return None


class RunLogger:
    def __init__(
        self,
        root: Path,
        model: str,
        backend: str,
        tag: str = "",
        config: dict[str, Any] | None = None,
        project_root: Path | None = None,
    ) -> None:
        started = datetime.now(timezone.utc)
        run_id = f"{started:%Y%m%d-%H%M%S}_{_slug(model)}"

        if tag:
            run_id += f"_{_slug(tag)}"

        self.run_id = run_id
        self.dir = root / run_id
        self.dir.mkdir(parents=True, exist_ok=True)

        self._t0 = time.monotonic()
        self._seq = 0
        self._scopes: list[dict[str, Any]] = []
        self.counters: Counter[str] = Counter()
        self.token_totals: Counter[str] = Counter()
        self._events = open(self.dir / "events.jsonl", "a", encoding="utf-8")

        self.meta: dict[str, Any] = {
            "run_id": run_id,
            "started_at": started.isoformat(),
            "model": model,
            "backend": backend,
            "tag": tag,
            "config": config or {},
            "git_commit": _git_commit(project_root or Path.cwd()),
            "git_dirty": _git_dirty(project_root or Path.cwd()),
            "agda_version": _agda_version(),
            "python": platform.python_version(),
            "hostname": platform.node(),
            "cwd": os.getcwd(),
        }

        (self.dir / "meta.json").write_text(json.dumps(self.meta, indent=2, default=_jsonable))

    # -- scopes ------------------------------------------------------------

    @contextmanager
    def scope(self, **fields: Any) -> Iterator[None]:
        self._scopes.append(fields)
        try:
            yield
        finally:
            self._scopes.pop()

    def _scope_fields(self) -> dict[str, Any]:
        merged: dict[str, Any] = {}

        for scope in self._scopes:
            merged.update(scope)

        return merged

    # -- events ------------------------------------------------------------

    def event(self, kind: str, **fields: Any) -> dict[str, Any]:
        self._seq += 1
        self.counters[kind] += 1

        record: dict[str, Any] = {
            "seq": self._seq,
            "ts": datetime.now(timezone.utc).isoformat(),
            "t": round(time.monotonic() - self._t0, 3),
            "kind": kind,
        }
        record.update(self._scope_fields())
        record.update(fields)

        if kind == "llm_call":
            for key in ("prompt_tokens", "output_tokens"):
                if isinstance(fields.get(key), int):
                    self.token_totals[key] += fields[key]

        self._events.write(json.dumps(record, default=_jsonable, ensure_ascii=False) + "\n")
        self._events.flush()

        return record

    # -- lifecycle ---------------------------------------------------------

    def finish(self, result: Any = None, **fields: Any) -> Path:
        elapsed = round(time.monotonic() - self._t0, 3)

        summary: dict[str, Any] = {
            "run_id": self.run_id,
            "model": self.meta["model"],
            "backend": self.meta["backend"],
            "tag": self.meta["tag"],
            "started_at": self.meta["started_at"],
            "finished_at": datetime.now(timezone.utc).isoformat(),
            "elapsed_s": elapsed,
            "event_counts": dict(self.counters),
            "token_totals": dict(self.token_totals),
            "result": _jsonable(result) if dataclasses.is_dataclass(result) else result,
        }
        summary.update(fields)

        self.event("run_end", elapsed_s=elapsed, **{k: v for k, v in fields.items()})

        path = self.dir / "summary.json"
        path.write_text(json.dumps(summary, indent=2, default=_jsonable, ensure_ascii=False))
        self._events.close()

        return path


class NullRunLogger:
    """Stand-in when no run is active. Same surface, does nothing."""

    run_id = "<no-run>"
    dir = None

    @contextmanager
    def scope(self, **fields: Any) -> Iterator[None]:
        yield

    def event(self, kind: str, **fields: Any) -> dict[str, Any]:
        return {}

    def finish(self, result: Any = None, **fields: Any) -> None:
        return None


_current: RunLogger | NullRunLogger = NullRunLogger()


def set_run_logger(logger: RunLogger | NullRunLogger | None) -> None:
    global _current
    _current = logger or NullRunLogger()


def run_logger() -> RunLogger | NullRunLogger:
    return _current
