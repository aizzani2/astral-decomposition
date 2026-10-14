"""
deproof's command line: take a finished proof apart and write a report.

    python -m deproof FILE NAME [--checkout ROOT] [--line N]
                      [--granularity step|lemma|clause] [--compare OTHER_FILE]

writes reports/deproof/<library>/<file>/<NAME>.agda: the library's proof, its
decomposition (in comments) and the sketches as Agda checked them, every hole
commented with the term it replaced; and NAME.json beside it, with the same
data. With --checkout, FILE is relative to the checkout and the work happens
in a symlink mirror of it (data/checkout.py), so the checkout is never written to.

Over a dataset: python -m deproof.dataset (deproof/dataset.py).
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import subprocess
import textwrap
from dataclasses import dataclass
from pathlib import Path

from core.agda_source import declaration_span
from core.config import PROJECT_ROOT
from data.checkout import mirrored
from deproof.comparison import compare
from deproof.decompose import DEFAULT_CONGRUENCES, decompose
from deproof.decomposition import Decomposition
from deproof.sketch_export import export_sketch



def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Take a finished proof apart into its clauses, steps and lemmas."
    )
    parser.add_argument("file", help="Agda file; relative to --checkout when one is given.")
    parser.add_argument("name", help="Declaration to take apart.")
    parser.add_argument("--line", type=int, default=None,
                        help="Line of the declaration, when its name occurs more than once.")
    parser.add_argument("--checkout", metavar="ROOT",
                        help="Library checkout FILE belongs to. Work happens in a symlink "
                             "mirror of it, so the checkout is never written to.")
    parser.add_argument("--include", default="src",
                        help="With --checkout: the include directory, relative to ROOT.")
    parser.add_argument("--granularity", action="append", choices=("clause", "step", "lemma"),
                        default=[], help="Sketches to export (default: step and lemma).")
    parser.add_argument("--compare", metavar="OTHER_FILE",
                        help="Another file proving the same declaration name.")
    parser.add_argument("--congruence", action="append", default=[],
                        help="Extra congruence names to see through (cong always is).")
    parser.add_argument("--out-dir", default=str(PROJECT_ROOT / "reports" / "deproof"),
                        help="Where reports go: OUT_DIR/<library>/<file>/<name>.{agda,json}.")
    args = parser.parse_args(argv)

    congruences = DEFAULT_CONGRUENCES + tuple(args.congruence)

    if args.checkout:
        root = Path(args.checkout).resolve()
        where = _Origin(root.name, args.file, _commit(root))
        with mirrored(root, args.file) as tree:
            return _run(args, tree / args.file, str(tree / args.include), congruences, where)

    agda_file = Path(args.file).resolve()
    root = next((d for d in agda_file.parents if any(d.glob("*.agda-lib"))), agda_file.parent)
    where = _Origin(root.name, str(agda_file.relative_to(root)), _commit(root))
    return _run(args, agda_file, None, congruences, where)


@dataclass
class _Origin:
    library: str
    path: str
    commit: str


def _commit(root: Path) -> str:
    out = subprocess.run(["git", "-C", str(root), "rev-parse", "--short", "HEAD"],
                         capture_output=True, text=True)
    return out.stdout.strip()


def _run(
    args: argparse.Namespace,
    agda_file: Path,
    import_path: str | None,
    congruences: tuple[str, ...],
    origin: _Origin,
) -> int:
    decomposition = decompose(agda_file, args.name, import_path, congruences=congruences, line=args.line)
    source = agda_file.read_text()
    start, _, end, column = declaration_span(source, args.name, args.line)
    proof = "".join(l[min(column, len(l) - len(l.lstrip())):] for l in source[start:end].splitlines(True))

    sketches = [
        export_sketch(
            agda_file, args.name, granularity, import_path, decomposition=decomposition,
            annotate=True, congruences=congruences, line=args.line,
        )
        for granularity in args.granularity or ["step", "lemma"]
    ]

    comparison = ""
    if args.compare:
        other = decompose(Path(args.compare).resolve(), args.name, import_path, congruences=congruences)
        comparison = compare(decomposition, other).render(Path(args.file).stem, Path(args.compare).stem)

    agda_out = write_report(
        Path(args.out_dir), origin, source.count("\n", 0, start) + 1,
        proof.strip(), decomposition, sketches, comparison,
    )
    print(f"{args.name}: {len(decomposition.clauses)} clause(s), "
          f"{decomposition.n_steps - decomposition.n_definitional} step(s), "
          f"{len(decomposition.lemmas)} lemma(s) -> {agda_out}")
    return 0


def write_report(
    out_dir: Path,
    origin: _Origin,
    line: int,
    proof: str,
    decomposition: Decomposition,
    sketches: list,
    comparison: str = "",
) -> Path:
    """
    The decomposition as an Agda file to read (and a JSON file beside it):
    the library's proof, its decomposition in comments, and each sketch as
    Agda checked it, every hole commented with what it replaced. An excerpt:
    it was checked in place in its module, not on its own.
    """

    stem = Path(origin.path)
    stem = stem.with_name(stem.name.split(".")[0])
    target = out_dir / origin.library / stem / (decomposition.name.replace("/", "∕") or "_")
    target.parent.mkdir(parents=True, exist_ok=True)

    def comment(text: str) -> str:
        return "\n".join(f"-- {l}".rstrip() for l in text.splitlines())

    rule = "-" * 72
    parts = [
        f"-- deproof: {decomposition.name}",
        f"-- {origin.library} {origin.path}:{line}" + (f" @ {origin.commit}" if origin.commit else ""),
        "-- An excerpt for reading: each part was checked by Agda in place, in its module.",
        "",
        rule, "-- The library's proof", "", proof, "",
        rule, "-- Its decomposition", "", comment(decomposition.render()), "",
    ]

    for sketch in sketches:
        status = "valid" if sketch.valid else "INVALID"
        if sketch.valid and sketch.warnings:
            status = "valid, with warnings"
        lemmas = f"; lemmas {', '.join(sketch.lemmas)}" if sketch.lemmas else ""
        parts += [rule, f"-- {sketch.granularity.capitalize()} sketch ({status}, "
                        f"{len(sketch.holes)} hole(s){lemmas})", ""]
        parts += [comment("\n".join(
            [f"problem: {p}" for p in sketch.problems] + [f"warning: {w}" for w in sketch.warnings]
            + [f"note: {n}" for n in sketch.notes]
        ))] if (sketch.problems or sketch.warnings or sketch.notes) else []
        parts += [textwrap.dedent(sketch.excerpt).strip("\n"), ""]

    if comparison:
        parts += [rule, "-- Compared with --compare", "", comment(comparison), ""]

    agda_out = target.with_suffix(".agda")
    agda_out.write_text("\n".join(parts).rstrip() + "\n")
    target.with_suffix(".json").write_text(json.dumps({
        "origin": dataclasses.asdict(origin), "line": line, "proof": proof,
        "decomposition": dataclasses.asdict(decomposition),
        "sketches": [
            {k: getattr(sk, k) for k in ("granularity", "excerpt", "holes", "lemmas",
                                         "problems", "warnings", "notes")} | {"valid": sk.valid}
            for sk in sketches
        ],
        "comparison": comparison or None,
    }, ensure_ascii=False, indent=1))
    return agda_out


if __name__ == "__main__":
    raise SystemExit(main())
