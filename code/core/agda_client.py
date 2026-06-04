import json
import subprocess
from pathlib import Path
from typing import Any

from core.proof_state import AgdaCheckResult, AgdaGoal, AgdaLoadResult


MAX_JSON_LINES = 300
AGDA_IMPORT_PATH = "agda_files"


def clean_json_line(line: str) -> str:
    line = line.strip()

    if line.startswith("JSON> "):
        return line[len("JSON> ") :]

    return line


def send_command(proc: subprocess.Popen[str], command: str) -> None:
    if proc.stdin is None:
        raise RuntimeError("Agda process has no stdin.")

    proc.stdin.write(command + "\n")
    proc.stdin.flush()


def _extract_goal_id(goal: dict[str, Any]) -> int | None:
    constraint = goal.get("constraintObj", {})
    goal_id = constraint.get("id")

    if isinstance(goal_id, int):
        return goal_id

    return None


def _find_range_for_goal_id(
    interaction_points: list[dict[str, Any]],
    goal_id: int | None,
) -> Any | None:
    if goal_id is None:
        return None

    for point in interaction_points:
        if point.get("id") != goal_id:
            continue

        ranges = point.get("range", [])

        if not ranges:
            return None

        return ranges[0]

    return None


def _read_agda_load_response(
    proc: subprocess.Popen[str],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], str | None]:
    goals: list[dict[str, Any]] = []
    interaction_points: list[dict[str, Any]] = []
    error_message: str | None = None

    if proc.stdout is None:
        raise RuntimeError("Agda process has no stdout.")

    for _ in range(MAX_JSON_LINES):
        raw = proc.stdout.readline()

        if not raw:
            break

        line = clean_json_line(raw)

        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue

        kind = obj.get("kind")

        if kind == "DisplayInfo":
            info = obj.get("info", {})
            info_kind = info.get("kind")

            if info_kind == "AllGoalsWarnings":
                goals = info.get("visibleGoals", [])

            elif info_kind == "Error":
                error = info.get("error", {})
                error_message = error.get("message")

        elif kind == "InteractionPoints":
            interaction_points = obj.get("interactionPoints", [])

            if goals or error_message is not None:
                break

    return goals, interaction_points, error_message


def _start_agda_interaction_process() -> subprocess.Popen[str]:
    return subprocess.Popen(
        ["agda", "-i", AGDA_IMPORT_PATH, "--interaction-json"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        bufsize=1,
    )


def _stop_process(proc: subprocess.Popen[str]) -> None:
    proc.terminate()

    try:
        proc.wait(timeout=2)
    except subprocess.TimeoutExpired:
        proc.kill()


def load_agda_and_get_first_goal(filename: Path) -> AgdaLoadResult:
    absolute_filename = str(filename.resolve())
    proc = _start_agda_interaction_process()

    try:
        send_command(
            proc,
            f'IOTCM "{absolute_filename}" None Direct '
            f'(Cmd_load "{absolute_filename}" [])',
        )

        goals, interaction_points, error_message = _read_agda_load_response(proc)

    finally:
        _stop_process(proc)

    if error_message is not None:
        return AgdaLoadResult(
            kind="error",
            message=error_message,
        )

    if not goals:
        return AgdaLoadResult(kind="no-goals")

    first_goal = goals[0]
    goal_id = _extract_goal_id(first_goal)
    goal_range = _find_range_for_goal_id(interaction_points, goal_id)

    return AgdaLoadResult(
        kind="goal",
        goal=AgdaGoal(
            id=goal_id,
            type=first_goal.get("type", ""),
            range=goal_range,
        ),
    )


def run_plain_agda(filename: Path) -> AgdaCheckResult:
    result = subprocess.run(
        ["agda", "-i", AGDA_IMPORT_PATH, str(filename)],
        capture_output=True,
        text=True,
    )

    return AgdaCheckResult(
        success=result.returncode == 0,
        output=result.stdout + result.stderr,
    )