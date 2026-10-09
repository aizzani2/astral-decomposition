"""
Where a DSP run keeps its lemmas.

`prove_dsp` postulates the lemmas a sketch declares, checks the sketch against
them, then proves each lemma by recursing and keeps the proved declaration.
Where those lemmas live depends on the problem:

    HelpersFileLayout   the test setup: lemmas live in their own module
                        (Tests.Helpers), which the target imports; each lemma
                        is proved in a one-declaration file (Tests.HelperGoal)

    InFileLayout        a theorem inside a library file: its lemmas can need the
                        module's parameters and private names, so they live in
                        the same file, just above the declaration being proved;
                        each lemma is proved in place

Both offer the same operations, used at the same points of the pipeline.
"""

from __future__ import annotations

import re
from pathlib import Path

from core.proof_files import (
    append_helper_declaration,
    append_postulates,
    restore_file,
    save_file,
    write_helper_goal_file,
)
from core.proof_state import ProofObligation
from util.agda_source import declaration_span
from util.source_edit import ensure_import, replace_top_level_decl

HELPERS_IMPORT = "open import Tests.Helpers"

REGION_START = "-- dsp: lemmas"
REGION_END = "-- dsp: end of lemmas"


class HelpersFileLayout:
    """Lemmas in Tests.Helpers, proved one at a time in Tests.HelperGoal."""

    def __init__(self, helpers_file: Path, helper_goal_file: Path) -> None:
        self.helpers_file = helpers_file
        self.helper_goal_file = helper_goal_file

    def snapshot(self) -> str | None:
        return save_file(self.helpers_file)

    def restore(self, state: str | None) -> None:
        restore_file(self.helpers_file, state)

    def text(self) -> str:
        return self.helpers_file.read_text() if self.helpers_file.exists() else ""

    def has_postulates(self) -> bool:
        return "postulate" in self.text()

    def postulate(self, lemmas: list[ProofObligation], before: str) -> None:
        append_postulates(self.helpers_file, lemmas)

    def add_proved(self, declaration: str) -> None:
        append_helper_declaration(helpers_file=self.helpers_file, declaration=declaration)

    def install(self, source: str, target: str, sketch: str) -> str:
        """The target file with `sketch` in place of `target`'s declaration."""
        return replace_top_level_decl(
            source=ensure_import(source, HELPERS_IMPORT), name=target, replacement=sketch
        )

    def render(self, source: str) -> str:
        return source  # the lemmas live in another file

    def lemma_goal(self, obligation: ProofObligation, working_source: str) -> Path:
        write_helper_goal_file(helper_goal_file=self.helper_goal_file, obligation=obligation)
        return self.helper_goal_file

    def declaration_of(self, source: str, name: str) -> str:
        lines = source.splitlines()
        start = next((i for i, line in enumerate(lines) if line.startswith(f"{name} :")), None)

        if start is None:
            raise ValueError(f"Could not find declaration of {name} in the proved file.")

        end = len(lines)
        for index in range(start + 1, len(lines)):
            line = lines[index]
            if line and not line.startswith((" ", "\t", "--")) and " : " in line:
                end = index
                break

        return "\n".join(lines[start:end]).strip()

    def lemma_at_error(self, message: str, lemmas: list[ProofObligation]) -> str | None:
        """The postulated lemma an Agda error points at, if it is in the helpers."""

        lines = self.text().splitlines()
        names = {l.name for l in lemmas}

        # Agda may report several errors; any of them can be the lemma's.
        for where in re.finditer(rf"{re.escape(self.helpers_file.name)}:(\d+)[.,]\d+", message):
            row = int(where.group(1))
            if 0 < row <= len(lines):
                head = lines[row - 1].strip().split(" : ", 1)[0]
                if head in names:
                    return head
        return None


class InFileLayout:
    """
    Lemmas inside the theorem's own file, in a region just above the
    declaration being proved. The file is kept to what the proof can see: it
    is cut after the theorem, since nothing below it is needed and what used
    it would only be broken while it is a sketch.

    The file is always `prefix + region + declaration`: `prefix` is the file
    above the theorem, `region` the lemmas (postulated or proved, in
    dependency order), and the declaration is whatever is being proved: the
    theorem, or a lemma when the run recurses into one.
    """

    def __init__(self, agda_file: Path, name: str, line: int | None = None) -> None:
        """Set the file up to prove `name`: the theorem's clauses become one hole."""

        self.agda_file = agda_file
        original = agda_file.read_text()
        sig_start, body_start, _, column = declaration_span(original, name, line)

        self.name = name
        self.column = column
        self.pad = " " * column
        # The copy is imported by nothing, so it can give up `--safe`, which
        # forbids the postulates lemmas are checked under.
        self.prefix = re.sub(r"(\{-#\s*OPTIONS\b[^#]*?)\s+--safe\b", r"\1", original[:sig_start])
        # A literate file cut inside a code block needs the block closed.
        fences = sum(1 for l in self.prefix.splitlines() if l.strip().startswith("```"))
        self.suffix = "\n```\n" if fences % 2 else "\n"
        self.blocks: list[tuple[str, str, bool]] = []   # (name, dedented text, postulated)

        signature = _dedent(original[sig_start:body_start], column).rstrip("\n")
        self.signature = signature
        agda_file.write_text(self._compose(f"{signature}\n{name} = {{!!}}"))

    # -- state -------------------------------------------------------------

    def snapshot(self) -> list[tuple[str, str, bool]]:
        return list(self.blocks)

    def restore(self, state: list[tuple[str, str, bool]]) -> None:
        self.blocks = list(state)

    def text(self) -> str:
        return "\n\n".join(text for _, text, _ in self.blocks)

    def has_postulates(self) -> bool:
        return any(postulated for _, _, postulated in self.blocks)

    def postulate(self, lemmas: list[ProofObligation], before: str) -> None:
        new = [
            (l.name, f"postulate\n  {l.name} : {l.signature}", True)
            for l in lemmas
        ]
        names = [n for n, _, _ in self.blocks]
        index = names.index(before) if before in names else len(self.blocks)
        self.blocks[index:index] = new

    def add_proved(self, declaration: str) -> None:
        name = declaration.split(":", 1)[0].strip()
        self.blocks = [b for b in self.blocks if b[0] != name] + [(name, declaration.strip(), False)]

    # -- text --------------------------------------------------------------

    def install(self, source: str, target: str, sketch: str) -> str:
        return self._compose(sketch)

    def render(self, source: str) -> str:
        return self._compose(self._declaration_part(source))

    def lemma_goal(self, obligation: ProofObligation, working_source: str) -> Path:
        self.agda_file.write_text(self._compose(
            f"{obligation.name} : {obligation.signature}\n{obligation.name} = {{!!}}"
        ))
        return self.agda_file

    def declaration_of(self, source: str, name: str) -> str:
        sig_start, _, end, column = declaration_span(source, name)
        return _dedent(source[sig_start:end], column).strip()

    def lemma_at_error(self, message: str, lemmas: list[ProofObligation]) -> str | None:
        names = {l.name for l in lemmas}
        spans: list[tuple[int, int, str, bool]] = []
        line = self.prefix.count("\n") + 2          # first line after REGION_START

        for name, text, postulated in self.blocks:
            height = text.count("\n") + 2           # text and the blank line after it
            spans.append((line, line + height, name, postulated))
            line += height

        # Agda may report several errors; any of them can be the lemma's.
        for where in re.finditer(r":(\d+)[.,]\d+", message):
            row = int(where.group(1))
            for first, last, name, postulated in spans:
                if first <= row < last and postulated and name in names:
                    return name
        return None

    def _compose(self, declaration: str) -> str:
        pad = self.pad
        region = "".join(f"{_indent(text, pad)}\n\n" for _, text, _ in self.blocks)
        return (
            f"{self.prefix}{pad}{REGION_START}\n{region}{pad}{REGION_END}\n"
            f"{_indent(declaration.strip(chr(10)), pad)}{self.suffix}"
        )

    def _declaration_part(self, source: str) -> str:
        """The declaration being proved, dedented, from a composed file text."""

        end_marker = f"{self.pad}{REGION_END}\n"
        start = source.index(end_marker) + len(end_marker) if end_marker in source else len(self.prefix)
        tail = source[start:]
        if self.suffix.strip() and tail.endswith(self.suffix):
            tail = tail[: -len(self.suffix)]
        return _dedent(tail, self.column)


def _indent(text: str, pad: str) -> str:
    return "\n".join(pad + line if line.strip() else line for line in text.split("\n"))


def _dedent(text: str, column: int) -> str:
    return "".join(
        line[min(column, len(line) - len(line.lstrip())):]
        for line in text.splitlines(keepends=True)
    )


Layout = HelpersFileLayout | InFileLayout

