"""
Agda interaction layer.

Two things this adds over the previous single-shot version:

1. `AgdaSession` keeps one `agda --interaction-json` process alive, so we can
   load a file once and then ask follow-up questions about specific holes
   (goal + context, and `auto`). Restarting Agda per question is both slow and
   useless for auto, which needs the interaction points from the same load.

2. `check_sketch` distinguishes "this skeleton is wrong" from "this skeleton is
   right but incomplete". That distinction is the whole point of a proof
   sketch: a file full of holes is a *success* at the sketch stage, and Agda
   reports it as warnings (unsolved interaction metas) rather than errors.
"""

from __future__ import annotations

import json
import re
import subprocess
import queue
import threading
import time
from pathlib import Path
from typing import Any

from core.config import (
    AGDA_IMPORT_PATH,
    AGDA_TIMEOUT_SECONDS,
    MIMER_TIMEOUT_SECONDS,
)
from core.run_log import run_logger
from core.proof_state import (
    AgdaCheckResult,
    AgdaGoal,
    AgdaLoadResult,
    ContextEntry,
    SketchCheckResult,
)


MAX_JSON_LINES = 2000


def clean_json_line(line: str) -> str:
    line = line.strip()

    if line.startswith("JSON> "):
        return line[len("JSON> ") :]

    return line


# ---------------------------------------------------------------------------
# Session
# ---------------------------------------------------------------------------


class AgdaSession:
    """
    One live `agda --interaction-json` process, scoped to one file.


    Usage:
        with AgdaSession(path) as session:
            result = session.load()
            term = session.auto(goal_id=0)
    """

    def __init__(
        self,
        filename: Path,
        import_path: str = AGDA_IMPORT_PATH,
        timeout: int = AGDA_TIMEOUT_SECONDS,
    ) -> None:
        timeout = max(timeout, MIMER_TIMEOUT_SECONDS + 10)
        self.filename = filename
        self.absolute = str(filename.resolve())
        self.import_path = import_path
        self.timeout = timeout
        self.proc: subprocess.Popen[str] | None = None

    def __enter__(self) -> "AgdaSession":
        self.proc = subprocess.Popen(
            ["agda", "-i", self.import_path, "--interaction-json"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        self._lines: queue.Queue[str | None] = queue.Queue()
        self._stderr: list[str] = []

        def pump_stdout() -> None:
            for line in self.proc.stdout:      # type: ignore[union-attr]
                self._lines.put(line)
            self._lines.put(None)              # EOF sentinel

        def pump_stderr() -> None:
            for line in self.proc.stderr:      # type: ignore[union-attr]
                self._stderr.append(line)

        for pump in (pump_stdout, pump_stderr):
            thread = threading.Thread(target=pump, daemon=True)
            thread.start()
        return self

    def __exit__(self, *exc: object) -> None:
        self.stop()

    def stop(self) -> None:
        if self.proc is None:
            return

        self.proc.terminate()

        try:
            self.proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.proc.kill()

        self.proc = None

    # -- low level ---------------------------------------------------------

    def _send(self, command: str) -> None:
        if self.proc is None or self.proc.stdin is None:
            raise RuntimeError("Agda session is not running.")

        payload = f'IOTCM "{self.absolute}" None Direct ({command})\n'
        self.proc.stdin.write(payload)
        self.proc.stdin.flush()

    def _read_objects(self, stop_when: Any) -> list[dict[str, Any]]:
        """Read JSON objects until stop_when(objects) is true or we run dry."""
        objects: list[dict[str, Any]] = []
        deadline = time.monotonic() + self.timeout

        while len(objects) < MAX_JSON_LINES:
            remaining = deadline - time.monotonic()

            if remaining <= 0:
                raise TimeoutError(
                    f"Agda produced no usable response within {self.timeout}s "
                    f"for {self.filename}.\n"
                    f"stderr:\n{''.join(self._stderr[-40:])}"
                )

            try:
                raw = self._lines.get(timeout=min(remaining, 1.0))
            except queue.Empty:
                continue

            if raw is None:  # Agda exited
                break

            try:
                obj = json.loads(clean_json_line(raw))
            except json.JSONDecodeError:
                continue

            objects.append(obj)

            if stop_when(objects):
                break

        return objects

    # -- commands ----------------------------------------------------------

    def load(self) -> AgdaLoadResult:
        self._send(f'Cmd_load "{self.absolute}" []')

        def done(objects: list[dict[str, Any]]) -> bool:
            return any(
                o.get("kind") == "DisplayInfo"
                and o.get("info", {}).get("kind") in ("AllGoalsWarnings", "Error")
                for o in objects
            )

        objects = self._read_objects(done)
        return _interpret_load(objects)

    def goal_context(self, goal_id: int) -> list[ContextEntry]:
        """Ask Agda for the variables in scope at one hole."""

        self._send(f'Cmd_goal_type_context Normalised {goal_id} noRange ""')

        objects = self._read_objects(
            lambda objs: any(o.get("kind") == "DisplayInfo" for o in objs)
        )

        return _interpret_context(objects)

    def auto(
        self,
        goal_id: int,
        hints: list[str] | None = None,
        timeout: int = MIMER_TIMEOUT_SECONDS,
    ) -> str | None:
        """
        Run Agda's automated prover (Mimer in Agda >= 2.6.4, Agsy before that)
        on one hole. Returns the proof term it found, or None.

        This is our stand-in for Sledgehammer. Mimer only uses local variables,
        constructors and recursive calls on its own; every lemma it may apply
        has to be passed by name in `hints`. A hint that is not in scope makes
        Agda return an Error, so callers should filter hints and retry bare.
        """

        args = [f"-t {int(timeout)}"] + [h for h in (hints or []) if h.strip()]
        argument = " ".join(args)

        self._send(f'Cmd_autoOne {goal_id} noRange "{argument}"')

        objects = self._read_objects(
            lambda objs: any(
                o.get("kind") in ("GiveAction", "MakeCase")
                or (
                    o.get("kind") == "DisplayInfo"
                    and o.get("info", {}).get("kind") in ("Auto", "Error")
                )
                for o in objs
            )
        )

        return _interpret_auto(objects)

    def auto_list(
        self,
        goal_id: int,
        hints: list[str] | None = None,
        timeout: int = MIMER_TIMEOUT_SECONDS,
        skip: int = 0,
    ) -> list[str]:
        """
        Mimer's list mode (`-l`): up to ten candidate terms, best first.

        Mimer only typechecks candidates; it does not run the termination
        checker, so its top pick can be a non-structural recursive call that
        Agda then rejects. Trying the rest of the list in order is how the
        hammer recovers from that.
        """

        args = [f"-t {int(timeout)}", "-l"]

        if skip:
            args.append(f"-s {int(skip)}")

        args += [h for h in (hints or []) if h.strip()]

        self._send(f'Cmd_autoOne {goal_id} noRange "{" ".join(args)}"')

        objects = self._read_objects(
            lambda objs: any(
                o.get("kind") == "GiveAction"
                or (
                    o.get("kind") == "DisplayInfo"
                    and o.get("info", {}).get("kind") in ("Auto", "Error")
                )
                for o in objs
            )
        )

        error = _auto_error(objects)

        if error is not None:
            raise AutoError(error)

        for obj in objects:
            if obj.get("kind") == "GiveAction":
                # A single solution comes back as a give, not a listing.
                result = obj.get("giveResult", {})
                term = result.get("str") if isinstance(result, dict) else result
                return [term.strip()] if isinstance(term, str) and term.strip() else []

            if obj.get("kind") == "DisplayInfo" and obj.get("info", {}).get("kind") == "Auto":
                return parse_auto_listing(obj["info"].get("info") or "")

        return []


# ---------------------------------------------------------------------------
# Response interpretation
# ---------------------------------------------------------------------------


def _extract_goal_id(goal: dict[str, Any]) -> int | None:
    constraint = goal.get("constraintObj", {})
    goal_id = constraint.get("id")

    if isinstance(goal_id, int):
        return goal_id

    goal_id = goal.get("id")

    return goal_id if isinstance(goal_id, int) else None


def _range_for_goal_id(
    interaction_points: list[dict[str, Any]],
    goal_id: int | None,
) -> Any | None:
    if goal_id is None:
        return None

    for point in interaction_points:
        if point.get("id") != goal_id:
            continue

        ranges = point.get("range", [])

        return ranges[0] if ranges else None

    return None


def _interpret_load(objects: list[dict[str, Any]]) -> AgdaLoadResult:
    goals: list[dict[str, Any]] = []
    interaction_points: list[dict[str, Any]] = []
    errors: list[str] = []
    warnings: list[str] = []
    fatal: str | None = None

    for obj in objects:
        kind = obj.get("kind")

        if kind == "InteractionPoints":
            interaction_points = obj.get("interactionPoints", [])

        elif kind == "DisplayInfo":
            info = obj.get("info", {})
            info_kind = info.get("kind")

            if info_kind == "AllGoalsWarnings":
                goals = info.get("visibleGoals", [])
                errors = _messages(info.get("errors", []))
                warnings = _messages(info.get("warnings", []))

            elif info_kind == "Error":
                fatal = info.get("error", {}).get("message", "") or "Unknown Agda error."

    if fatal is not None:
        return AgdaLoadResult(kind="error", message=fatal)

    if errors:
        return AgdaLoadResult(kind="error", message="\n".join(errors), warnings=warnings)

    parsed_goals: list[AgdaGoal] = []

    for raw_goal in goals:
        goal_id = _extract_goal_id(raw_goal)
        goal_range = _range_for_goal_id(interaction_points, goal_id)

        if goal_range is None:
            own = raw_goal.get("constraintObj", {}).get("range", [])
            goal_range = own[0] if own else None

        parsed_goals.append(
            AgdaGoal(id=goal_id, type=raw_goal.get("type", ""), range=goal_range)
        )

    if not parsed_goals:
        return AgdaLoadResult(kind="no-goals", warnings=warnings)

    parsed_goals.sort(key=lambda g: (g.id is None, g.id))

    return AgdaLoadResult(kind="goal", goals=parsed_goals, warnings=warnings)


def _messages(items: Any) -> list[str]:
    """Agda reports errors/warnings as either strings or {message: ...} dicts."""

    if isinstance(items, str):
        return [items] if items.strip() else []

    if not isinstance(items, list):
        return []

    out: list[str] = []

    for item in items:
        if isinstance(item, str) and item.strip():
            out.append(item)
        elif isinstance(item, dict):
            message = item.get("message") or item.get("msg") or ""
            if isinstance(message, str) and message.strip():
                out.append(message)

    return out


def _interpret_context(objects: list[dict[str, Any]]) -> list[ContextEntry]:
    entries: list[ContextEntry] = []

    for obj in objects:
        if obj.get("kind") != "DisplayInfo":
            continue

        info = obj.get("info", {})
        goal_info = info.get("goalInfo", info)

        for raw in goal_info.get("entries", []) or []:
            if not isinstance(raw, dict):
                continue

            name = (
                raw.get("reifiedName")
                or raw.get("originalName")
                or raw.get("name")
                or ""
            )
            binding = raw.get("binding") or raw.get("type") or ""

            if not name:
                continue

            entries.append(
                ContextEntry(
                    name=str(name),
                    type=str(binding).lstrip(": ").strip(),
                    in_scope=bool(raw.get("inScope", True)),
                )
            )

    return entries


def parse_auto_listing(text: str) -> list[str]:
    """
    Parse `Listing solution(s) 0-9\n0  term\n(continued)\n1  term ...`.
    Continuation lines of a multi-line term do not start with an index.
    """

    solutions: list[str] = []
    current: list[str] = []
    index_line = re.compile(r"^(\d+)\s{2,}(.*)$")

    for line in text.splitlines():
        if line.startswith("Listing ") or line.startswith("No solution"):
            continue

        match = index_line.match(line)

        if match:
            if current:
                solutions.append(" ".join(current))
            current = [match.group(2).strip()]
        elif current and line.strip():
            current.append(line.strip())

    if current:
        solutions.append(" ".join(current))

    return solutions


class AutoError(RuntimeError):
    """Agda rejected the auto command itself (typically an out-of-scope hint)."""


def _auto_error(objects: list[dict[str, Any]]) -> str | None:
    for obj in objects:
        if obj.get("kind") != "DisplayInfo":
            continue

        info = obj.get("info", {})

        if info.get("kind") == "Error":
            return info.get("error", {}).get("message", "") or "Unknown Agda error."

    return None


def _interpret_auto(objects: list[dict[str, Any]]) -> str | None:
    error = _auto_error(objects)

    if error is not None:
        raise AutoError(error)

    for obj in objects:
        kind = obj.get("kind")

        if kind == "GiveAction":
            result = obj.get("giveResult", {})
            term = result.get("str") if isinstance(result, dict) else result

            if isinstance(term, str) and term.strip():
                return term.strip()

        if kind == "DisplayInfo":
            info = obj.get("info", {})

            if info.get("kind") != "Auto":
                continue

            message = info.get("info") or info.get("message") or ""

            if isinstance(message, str) and message.strip():
                if "No solution found" in message or "Timeout" in message:
                    return None

                # Agsy replies like: `Listing solution(s) 0-0` or the term.
                return None

        if kind == "SolveAll":
            for solution in obj.get("solutions", []) or []:
                expression = solution.get("expression")

                if isinstance(expression, str) and expression.strip():
                    return expression.strip()

    return None


# ---------------------------------------------------------------------------
# Convenience wrappers
# ---------------------------------------------------------------------------


def load_agda_and_get_first_goal(
    filename: Path,
    import_path: str = AGDA_IMPORT_PATH,
) -> AgdaLoadResult:
    with AgdaSession(filename, import_path=import_path) as session:
        return session.load()


def load_agda_and_get_all_goals(
    filename: Path,
    import_path: str = AGDA_IMPORT_PATH,
    with_context: bool = False,
) -> AgdaLoadResult:
    with AgdaSession(filename, import_path=import_path) as session:
        result = session.load()

        if with_context and result.kind == "goal":
            for goal in result.goals:
                if goal.id is None:
                    continue
                try:
                    goal.context = session.goal_context(goal.id)
                except Exception:  # context is a nicety, not a requirement
                    goal.context = []

        return result


def check_sketch(
    filename: Path,
    import_path: str = AGDA_IMPORT_PATH,
    with_context: bool = True,
) -> SketchCheckResult:
    """
    Typecheck a file that is allowed to contain holes.

    "holes" means the skeleton is well-typed and only the gaps are missing:
    this is the sketch-stage success condition.
    """

    started = time.monotonic()
    source = filename.read_text() if filename.exists() else None

    result = load_agda_and_get_all_goals(
        filename,
        import_path=import_path,
        with_context=with_context,
    )

    if result.kind == "error":
        out = SketchCheckResult(kind="error", message=result.message)
    elif result.kind == "no-goals":
        out = SketchCheckResult(kind="complete")
    else:
        out = SketchCheckResult(kind="holes", goals=result.goals)

    run_logger().event(
        "agda_check",
        mode="sketch",
        file=str(filename),
        source=source,
        result=out.kind,
        message=out.message,
        n_goals=len(out.goals),
        goals=[{"id": g.id, "type": g.type} for g in out.goals],
        warnings=result.warnings,
        duration_s=round(time.monotonic() - started, 3),
    )

    return out


def run_plain_agda(
    filename: Path,
    import_path: str = AGDA_IMPORT_PATH,
    timeout: int = AGDA_TIMEOUT_SECONDS,
) -> AgdaCheckResult:
    started = time.monotonic()
    source = filename.read_text() if filename.exists() else None

    try:
        result = subprocess.run(
            ["agda", "-i", import_path, str(filename)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        out = AgdaCheckResult(
            success=False,
            output=f"Agda timed out after {timeout}s on {filename}.",
            timed_out=True,
        )
    else:
        out = AgdaCheckResult(
            success=result.returncode == 0,
            output=result.stdout + result.stderr,
        )

    run_logger().event(
        "agda_check",
        mode="plain",
        file=str(filename),
        source=source,
        result="ok" if out.success else ("timeout" if out.timed_out else "error"),
        message=out.output,
        duration_s=round(time.monotonic() - started, 3),
    )

    return out
