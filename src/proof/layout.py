"""
Where a DSP run keeps its lemmas: in the theorem's own file, in a region just
above the declaration being proved.

`prove_dsp` postulates the lemmas a sketch declares, checks the sketch against
them, then proves each lemma by recursing and keeps the proved declaration.
A library theorem's lemmas can need the module's parameters and private
names, so they live in the same module; each lemma is proved in place.
"""

from __future__ import annotations

import re
from pathlib import Path

from core.proof_state import ProofObligation
from core.agda_source import declaration_span
from core.sketch_ops import mask_comments

# What a proof must not contain (Agda rejects them all under --safe).
UNSAFE_PRAGMA_RE = re.compile(
    r"\{-#\s*(?:TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|"
    r"OPTIONS|BUILTIN|COMPILE|FOREIGN|INJECTIVE|ETA)\b"
)
UNSAFE_WORD_RE = re.compile(r"(?<![^\s(){};])(?:postulate|primTrustMe|trustMe|primEraseEquality)(?![^\s(){};])")

REGION_START = "-- dsp: lemmas"
REGION_END = "-- dsp: end of lemmas"


class Layout:
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

    def __init__(
        self,
        agda_file: Path,
        name: str,
        line: int | None = None,
        hide: list[tuple[int, int]] | None = None,
    ) -> None:
        """
        Set the file up to prove `name`: the theorem's clauses become one hole.
        `hide` lists line ranges (1-based, inclusive) above the theorem to
        remove first: lemmas the run must do without.
        """

        self.agda_file = agda_file
        original = agda_file.read_text()

        if hide:
            original, line = _without_lines(original, hide, line)
        sig_start, body_start, _, column = declaration_span(original, name, line)

        self.name = name
        self.column = column
        self.pad = " " * column
        # The copy is imported by nothing, so it can give up `--safe`, which
        # forbids the postulates lemmas are checked under. The final check
        # puts it back (`checked`).
        self.safe_prefix = original[:sig_start]
        self.prefix = re.sub(r"(\{-#\s*OPTIONS\b[^#]*?)\s+--safe\b", r"\1", self.safe_prefix)
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

    def install(self, sketch: str) -> str:
        """The file with `sketch` as the declaration being proved."""
        return self._compose(sketch)

    def render(self, source: str) -> str:
        return self._compose(self._declaration_part(source))

    def checked(self, source: str) -> str:
        """`source` with the file's own options back, `--safe` included if it had it."""
        return self._compose(self._declaration_part(source), prefix=self.safe_prefix)

    def unsafe_constructs(self, source: str) -> list[str]:
        """
        What the run's own text (its lemmas and the declaration) uses that a
        proof must not: postulates, termination or positivity escapes, trustMe.
        For a file without `--safe`, which Agda would not catch.
        """

        text = self.text() + "\n" + self._declaration_part(source)
        code = mask_comments(text)
        found = [m.group(0).strip("{-# ") for m in UNSAFE_PRAGMA_RE.finditer(text)]
        found += [m.group(0) for m in UNSAFE_WORD_RE.finditer(code)]
        return list(dict.fromkeys(found))

    def lemma_goal(self, obligation: ProofObligation) -> None:
        """Make the lemma the declaration being proved, its proof one hole."""
        self.agda_file.write_text(self._compose(
            f"{obligation.name} : {obligation.signature}\n{obligation.name} = {{!!}}"
        ))

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

    def _compose(self, declaration: str, prefix: str | None = None) -> str:
        pad = self.pad
        region = "".join(f"{_indent(text, pad)}\n\n" for _, text, _ in self.blocks)
        return (
            f"{self.prefix if prefix is None else prefix}{pad}{REGION_START}\n{region}{pad}{REGION_END}\n"
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


def _without_lines(
    source: str, ranges: list[tuple[int, int]], line: int | None
) -> tuple[str, int | None]:
    """`source` without the given line ranges, and where `line` moved to."""

    drop = {n for start, end in ranges for n in range(start, end + 1)}
    lines = source.splitlines(keepends=True)
    kept = "".join(text for n, text in enumerate(lines, start=1) if n not in drop)

    if line is not None:
        line -= sum(1 for n in drop if n < line)

    return kept, line


def _indent(text: str, pad: str) -> str:
    return "\n".join(pad + line if line.strip() else line for line in text.split("\n"))


def _dedent(text: str, column: int) -> str:
    return "".join(
        line[min(column, len(line) - len(line.lstrip())):]
        for line in text.splitlines(keepends=True)
    )


