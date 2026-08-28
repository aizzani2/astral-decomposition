"""
Text-level operations on Agda proof sketches.

The key invariant everything here relies on: Agda numbers interaction points
in source order on a fresh load, so the i-th `{! ... !}` in the file is
interaction point i. That lets us line up goal types and contexts (which come
from the interaction protocol) with the in-line informal comments (which only
exist in the text).
"""

from __future__ import annotations

import re

from core.proof_state import SketchGap


HOLE_RE = re.compile(r"\{!.*?!\}", re.DOTALL)


def find_holes(source: str) -> list[tuple[int, int]]:
    """Return (start, end) character spans of every hole, in source order."""

    return [match.span() for match in HOLE_RE.finditer(source)]


def count_holes(source: str) -> int:
    return len(find_holes(source))


def replace_hole(source: str, hole_index: int, replacement: str) -> str:
    """Replace the hole_index-th hole with a term."""

    spans = find_holes(source)

    if hole_index < 0 or hole_index >= len(spans):
        raise IndexError(
            f"Hole index {hole_index} out of range (file has {len(spans)} holes)."
        )

    start, end = spans[hole_index]

    return source[:start] + replacement.strip() + source[end:]


def comment_before_hole(source: str, hole_index: int) -> str:
    """
    Recover the in-line informal comment attached to a hole.

    The sketch prompt asks the model to put the informal step in an Agda
    comment directly above the clause containing the hole, so we walk back over
    the current line and collect contiguous `--` lines.
    """

    spans = find_holes(source)

    if hole_index < 0 or hole_index >= len(spans):
        return ""

    start, _ = spans[hole_index]
    lines = source[:start].splitlines()

    comments: list[str] = []

    # Skip the (partial) line the hole is on, then walk upwards.
    for line in reversed(lines[:-1] if lines else []):
        stripped = line.strip()

        if stripped.startswith("--"):
            comments.append(stripped.lstrip("-").strip())
            continue

        if not stripped:
            if comments:
                break
            continue

        break

    return " ".join(reversed(comments))


def excerpt_around_hole(source: str, hole_index: int, context_lines: int = 6) -> str:
    """A window of the file around one hole, with the hole marked HERE."""

    spans = find_holes(source)

    if hole_index < 0 or hole_index >= len(spans):
        return source

    start, end = spans[hole_index]
    marked = source[:start] + "{! HERE !}" + source[end:]

    line_number = source[:start].count("\n")
    lines = marked.splitlines()

    lo = max(0, line_number - context_lines)
    hi = min(len(lines), line_number + context_lines + 1)

    return "\n".join(lines[lo:hi])


def build_gaps(source: str, goals: list) -> list[SketchGap]:
    """
    Zip the holes in the text with the goals Agda reported.

    If the counts disagree we still pair up as many as we can, in order, rather
    than failing: a mismatch usually means a hole inside a comment or string.
    """

    holes = find_holes(source)
    gaps: list[SketchGap] = []

    for index in range(min(len(holes), len(goals))):
        goal = goals[index]

        gaps.append(
            SketchGap(
                hole_index=index,
                goal_id=goal.id,
                goal_type=goal.type,
                context=list(getattr(goal, "context", []) or []),
                informal_hint=comment_before_hole(source, index),
            )
        )

    return gaps


def strip_comments(source: str) -> str:
    """Drop line comments; used when checking a sketch for leftover markers."""

    return "\n".join(
        line.split("--")[0] if line.strip().startswith("--") else line
        for line in source.splitlines()
    )


def available_names(*sources: str) -> str:
    """
    Collect top-level declaration names from Agda sources, to tell the model
    which lemmas it is actually allowed to cite. Cheap defence against the
    single most common failure mode: invented lemma names.
    """

    names: list[str] = []
    seen: set[str] = set()

    signature = re.compile(r"^([^\s(){};.]+)\s*:\s")
    data_or_record = re.compile(r"^\s*(data|record)\s+([^\s(){};.]+)")

    for source in sources:
        if not source:
            continue

        for line in source.splitlines():
            if line.startswith((" ", "\t")):
                # Indented signatures still matter (postulate blocks, where).
                stripped = line.strip()
                match = signature.match(stripped)
            else:
                stripped = line
                match = signature.match(stripped)

            if match:
                name = match.group(1)
            else:
                block = data_or_record.match(line)
                name = block.group(2) if block else ""

            if name and name not in seen and not name.startswith("--"):
                seen.add(name)
                names.append(name)

    return ", ".join(names)
