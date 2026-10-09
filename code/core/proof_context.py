import re
from pathlib import Path
from typing import Any

from core.agda_client import load_agda_and_get_first_goal
from core.config import AGDA_IMPORT_PATH, AGDA_TIMEOUT_SECONDS
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


BLOCK_HEADS = (
    "module ", "record ", "data ", "instance", "private", "abstract", "mutual",
    "opaque", "interleaved", "codata ", "postulate",
)
SIGNATURE_RE = re.compile(r"^(\s*)([^\s(){};]+)\s*:(?!:)\s")


def find_enclosing_top_level_decl_name(source: str, hole_line: int) -> str:
    """
    Given source text and a 1-indexed hole line, find the declaration the
    hole belongs to: the nearest signature above it at or left of every line
    in between. Declarations may be indented (inside `module _ ... where`);
    signatures inside a clause's own `where` block are skipped.

        theoremName : Type
        theoremName = ...
    """

    lines = source.splitlines()

    if hole_line < 1 or hole_line > len(lines):
        raise ValueError(
            f"Hole line {hole_line} is outside source range 1..{len(lines)}."
        )

    def indent(line: str) -> int:
        return len(line) - len(line.lstrip())

    def code(index: int) -> bool:
        stripped = lines[index].strip()
        return bool(stripped) and not stripped.startswith(("--", "{-"))

    def local_to_where(index: int) -> bool:
        """Whether the signature at `index` sits in some clause's `where` block."""
        column = indent(lines[index])
        for above in range(index - 1, -1, -1):
            if not code(above) or indent(lines[above]) > column:
                continue
            stripped = lines[above].strip()
            if stripped.startswith(BLOCK_HEADS):
                return False   # a module/record/data block, not a clause's where
            if stripped == "where" or stripped.startswith("where ") or stripped.endswith(" where"):
                return True
            if indent(lines[above]) < column:
                return False
        return False

    leftmost = indent(lines[hole_line - 1])

    for index in range(hole_line - 1, -1, -1):
        if not code(index):
            continue

        line = lines[index]
        match = SIGNATURE_RE.match(line)

        if (
            match and indent(line) <= leftmost
            and match.group(2) not in ("open", "import", "module", "infix", "infixl", "infixr")
            and not local_to_where(index)
        ):
            return match.group(2)

        leftmost = min(leftmost, indent(line))

    raise ValueError(f"Could not find enclosing declaration for line {hole_line}.")


def get_signature_line(source: str, target_name: str) -> str:
    """
    Return target_name's signature on one line, with its continuation lines
    (a signature may span several) joined.

    Example:
        plusZero : (n : Nat) → n + 0 ≡ n
    """

    prefix = f"{target_name} :"
    lines = source.splitlines()

    for index, line in enumerate(lines):
        stripped = line.strip()

        if not stripped.startswith(prefix):
            continue

        column = len(line) - len(line.lstrip())
        parts = [stripped]

        for follow in lines[index + 1:]:
            if follow.strip() and len(follow) - len(follow.lstrip()) > column:
                parts.append(follow.strip())
            else:
                break

        return " ".join(parts)

    raise ValueError(f"Could not find signature line for {target_name}.")


def infer_target_name_from_first_hole(
    agda_file: Path,
    import_path: str = AGDA_IMPORT_PATH,
    timeout: int = AGDA_TIMEOUT_SECONDS,
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
    load_result = load_agda_and_get_first_goal(agda_file, import_path=import_path, timeout=timeout)

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