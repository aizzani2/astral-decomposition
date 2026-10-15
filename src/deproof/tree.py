"""
The tree of lemmas behind a proof: the lemmas it uses that are defined
earlier in the same file, the lemmas those use, and so on.

    python -m deproof.tree FILE NAME [--checkout ROOT] [--line N] [--depth 2]

A node is a declaration; its children are the same-file declarations its
proof uses (in its clauses or its `where` block) that Agda says are defined
above it in this file, and that `is_lemma` accepts (the datasets classify
declarations, so definitions, which a theorem's meaning depends on, can be
left out). Lemmas from other modules are recorded as `imported` but not
expanded. Each node is taken apart with `decompose`, so it costs one Agda
load.

This is what deciding "what to hide" needs: the lemmas at depth 1 are the
proof's direct dependencies, depth 2 theirs, and so on.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable

from core.agda_source import WORD_RE, declaration_span
from deproof.decompose import DEPROOF_TIMEOUT_SECONDS, decompose, resolve_names

SIGNATURE_RE = re.compile(r"^[ \t]*([^\s(){};:]+)[ \t]*:(?!:)", re.MULTILINE)


@dataclass
class TreeNode:
    name: str
    line: int                  # its signature's line, 1-based
    end_line: int              # its last line
    depth: int                 # 0: the theorem
    parent: str | None
    children: list[str] = field(default_factory=list)
    imported: list[str] = field(default_factory=list)   # lemmas from other modules
    steps: int = 0
    trivial: bool = False      # every step holds by computation or refl
    type: str = ""             # as written in the file
    normal: str = ""           # normalised, for matching statements


def top_level_names(source: str) -> dict[str, list[int]]:
    """Every name with a signature line in `source`, with those lines (1-based)."""

    names: dict[str, list[int]] = {}

    for match in SIGNATURE_RE.finditer(source):
        names.setdefault(match.group(1), []).append(source.count("\n", 0, match.start()) + 1)

    return names


def lemma_tree(
    agda_file: Path,
    name: str,
    line: int | None = None,
    import_path: str | None = None,
    max_depth: int = 2,
    is_lemma: Callable[[str], bool] | None = None,
    timeout: int = DEPROOF_TIMEOUT_SECONDS,
) -> dict[str, TreeNode]:
    """The proof's same-file lemma tree, breadth first, down to `max_depth`."""

    source = agda_file.read_text()
    names = top_level_names(source)
    here = agda_file.resolve()
    nodes: dict[str, TreeNode] = {}
    queue: list[tuple[str, int | None, int, str | None, dict]] = [(name, line, 0, None, {})]

    while queue:
        node_name, node_line, depth, parent, known = queue.pop(0)

        if node_name in nodes:
            continue

        start, body, end, _ = declaration_span(source, node_name, node_line)
        sig_line = source.count("\n", 0, start) + 1
        end_line = source.count("\n", 0, end) + 1
        words = set(WORD_RE.findall(source[body:end]))
        candidates = {
            w for w in words
            if w != node_name and any(l < sig_line for l in names.get(w, []))
        }

        try:
            decomposition = decompose(
                agda_file, node_name, import_path, line=sig_line,
                extra_names=sorted(candidates), timeout=timeout,
            )
            sources, lemmas = decomposition.sources, set(decomposition.lemmas)
            steps = decomposition.n_steps - decomposition.n_definitional
            trivial = decomposition.n_steps > 0 and decomposition.n_definitional == decomposition.n_steps
        except ValueError:
            # Its clauses cannot be holed (unsolved constraints): resolve the
            # names on the file as it is; its steps stay unknown.
            sources = resolve_names(agda_file, sorted(candidates), import_path, timeout)
            lemmas, steps, trivial = set(sources), 0, False

        node = TreeNode(
            name=node_name, line=sig_line, end_line=end_line, depth=depth, parent=parent,
            steps=steps, trivial=trivial,
            type=known.get("type", ""), normal=known.get("normal", ""),
        )

        for used, info in sources.items():
            if info.get("what") != "defined name":
                continue
            local = Path(info["path"]).resolve() == here and info["line"] < sig_line
            if local and (is_lemma is None or is_lemma(used)):
                node.children.append(used)
                if depth < max_depth:
                    queue.append((used, info["line"], depth + 1, node_name, info))
            elif not local and used in lemmas:
                node.imported.append(used)

        nodes[node_name] = node

    return nodes


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("file", help="Agda file; relative to --checkout when one is given.")
    parser.add_argument("name")
    parser.add_argument("--line", type=int, default=None)
    parser.add_argument("--checkout", metavar="ROOT")
    parser.add_argument("--include", default="src")
    parser.add_argument("--depth", type=int, default=2)
    args = parser.parse_args(argv)

    def run(agda_file: Path, import_path: str | None) -> dict[str, TreeNode]:
        return lemma_tree(agda_file, args.name, args.line, import_path, args.depth)

    if args.checkout:
        from data.checkout import mirrored

        with mirrored(Path(args.checkout), args.file) as tree:
            nodes = run(tree / args.file, str(tree / args.include))
    else:
        nodes = run(Path(args.file).resolve(), None)

    for node in nodes.values():
        print(f"{'  ' * node.depth}{node.name}  (line {node.line}, {node.steps} step(s)"
              f"{', trivial' if node.trivial else ''})"
              + (f"  imports: {', '.join(node.imported)}" if node.imported else ""))
    print(json.dumps({n: dataclasses.asdict(v) for n, v in nodes.items()}, ensure_ascii=False, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
