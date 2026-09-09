from pathlib import Path
from typing import Any

from core.agda_client import load_agda_and_get_first_goal
from core.config import AGDA_IMPORT_PATH
from core.proof_state import AgdaGoal, AgdaLoadResult


def get_start_line_from_range(goal_range: Any) -> int:
    """
    Extract the starting line number from an Agda interaction range.

    Agda ranges usually look something like:
        {"start": {"line": 10, ...}, "end": {...}}

    but this function is defensive because the exact JSON shape can vary.
    """

    if isinstance(goal_range, dict):
        start = goal_range.get("start")

        if isinstance(start, dict):
            line = start.get("line")

            if isinstance(line, int):
                return line

        line = goal_range.get("startLine")

        if isinstance(line, int):
            return line

    raise ValueError(f"Could not extract start line from range: {goal_range}")


def find_enclosing_top_level_decl_name(source: str, hole_line: int) -> str:
    """
    Given source text and a 1-indexed hole line, find the nearest preceding
    top-level declaration name.

    This assumes top-level declarations start at column 0 and look like:

        theoremName : Type
        theoremName = ...

    We prefer a type signature line because that gives the declaration name.
    """

    lines = source.splitlines()

    if hole_line < 1 or hole_line > len(lines):
        raise ValueError(
            f"Hole line {hole_line} is outside source range 1..{len(lines)}."
        )

    for index in range(hole_line - 1, -1, -1):
        line = lines[index]

        if not line.strip():
            continue

        if line.startswith(" ") or line.startswith("\t"):
            continue

        if line.startswith("--"):
            continue

        if " : " in line:
            name, _signature = line.split(" : ", 1)
            name = name.strip()

            if name:
                return name

    raise ValueError(f"Could not find enclosing top-level declaration for line {hole_line}.")


def get_signature_line(source: str, target_name: str) -> str:
    """
    Return the exact top-level signature line for target_name.

    Example:
        plusZero : (n : Nat) → n + 0 ≡ n
    """

    prefix = f"{target_name} :"

    for line in source.splitlines():
        stripped = line.strip()

        if stripped.startswith(prefix):
            return stripped

    raise ValueError(f"Could not find signature line for {target_name}.")


def infer_target_name_from_first_hole(
    agda_file: Path,
    import_path: str = AGDA_IMPORT_PATH,
) -> tuple[str, AgdaGoal, AgdaLoadResult]:
    """
    Load an Agda file, get the first goal, and infer the enclosing
    top-level declaration name from the goal range.

    `import_path` must be the root the file lives under. Loading a file from
    one tree with another tree on the include path makes Agda see two
    candidates for the module and refuse with "Ambiguous module name".

    Returns:
        (target_name, goal, load_result)
    """

    source = agda_file.read_text()
    load_result = load_agda_and_get_first_goal(agda_file, import_path=import_path)

    if load_result.kind == "error":
        raise ValueError(
            f"Agda found an error before getting to a hole:\n{load_result.message}"
        )
    if load_result.kind == "no-goals":
        raise ValueError("No goals found. The file may already typecheck.")

    if load_result.goal is None:
        raise ValueError("Agda returned kind='goal' but no goal object.")

    goal = load_result.goal

    if goal.range is None:
        raise ValueError("No range found for the first hole.")

    hole_line = get_start_line_from_range(goal.range)

    target_name = find_enclosing_top_level_decl_name(
        source=source,
        hole_line=hole_line,
    )

    return target_name, goal, load_result