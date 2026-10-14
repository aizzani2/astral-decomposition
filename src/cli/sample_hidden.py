"""
Draw library theorems with lemmas to hide, for cli/run_dsp_dataset.py --level N.

    python -m cli.sample_hidden --n 24 --depth 2 --jobs 3 --out samples/hidden24.json

Theorems come from the held-out test split of agda-autoformalize-context,
and are ones whose proof uses lemmas defined above it in the same file,
nested at least `--depth` deep (a quick scan of the datasets finds them).
For each, deproof builds the lemma tree (deproof/tree.py), and for every
level k = 1..depth the lines to hide: the tree's lemmas at depth <= k, and
the declarations between them and the theorem that use them. A theorem is
kept when, at every level:

  * the file still loads with the theorem's proof as a hole once they are gone;
  * every hidden name is out of scope at that hole (not imported from elsewhere);
  * at most --max-collateral other declarations had to go with them;

and when deeper levels hide more, and its depth-1 lemmas are not all trivial
(proved by refl). Items carry the dataset fields, the `tree`, and `levels`:
{"1": {"hide": [[first, last], ...], "names": [...], "hidden": [...],
"statements": {lemma: normalised type}}, ...}.
"""

from __future__ import annotations

import argparse
import dataclasses
import itertools
import json
import random
import sys
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

from core.agda_client import AgdaSession, check_sketch
from core.agda_source import WORD_RE, declaration_span
from core.config import CHECKOUTS_ROOT, DATASETS_ROOT
from core.proof_files import preserved_file
from data.agda_data import checkout_for, load_rows
from data.checkout import mirrored
from deproof.decompose import where_defined
from deproof.tree import lemma_tree
from proof.layout import Layout

LEMMA_KINDS = ("lemma", "theorem")
SKIPPED_FLAGS = {"constructor", "generalize", "postulate", "field", "instance", "abstract"}
AGDA_TIMEOUT = 900


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--n", type=int, default=24)
    parser.add_argument("--depth", type=int, default=2, help="Levels 1..depth.")
    parser.add_argument("--max-collateral", type=int, default=3,
                        help="Other declarations a level may remove along with the lemmas.")
    parser.add_argument("--max-tries", type=int, default=72)
    parser.add_argument("--seed", type=int, default=11)
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--checkouts", default=str(CHECKOUTS_ROOT))
    parser.add_argument("--out", required=True)
    args = parser.parse_args(argv)

    candidates, kinds, declarations = find_candidates(args.depth, args.seed)
    tries = candidates[: args.max_tries]
    print(f"{len(candidates)} candidates; trying {len(tries)}", file=sys.stderr)

    accepted: dict[int, dict] = {}
    reasons: dict[str, int] = defaultdict(int)

    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        futures = {
            pool.submit(build, item, kinds[(item["repo"], item["path"])],
                        declarations[(item["repo"], item["path"])], args.depth,
                        args.max_collateral, args.checkouts): index
            for index, item in enumerate(tries)
        }
        for future in as_completed(futures):
            index = futures[future]
            try:
                item, reason = future.result()
            except Exception as error:
                item, reason = None, f"error: {type(error).__name__}"
            reasons[reason or "kept"] += 1
            name = tries[index]["name"]
            print(f"{name[:30]:<30} {reason or 'kept'}", file=sys.stderr, flush=True)
            if item is not None:
                accepted[index] = item

    sample = [accepted[i] for i in sorted(accepted)][: args.n]
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(sample, indent=1, ensure_ascii=False))
    print(f"{dict(reasons)}\n{len(sample)} theorems -> {out}", file=sys.stderr)
    return 0


def find_candidates(depth: int, seed: int) -> tuple[list[dict], dict, dict]:
    """
    Test-split theorems whose same-file lemma tree looks at least `depth`
    deep, by a scan of the datasets' text (deproof checks it properly later),
    shuffled and interleaved across repos. Also, per file, each declaration's
    kind and the lines of its signatures.
    """

    base = DATASETS_ROOT / "agda-autoformalize-context" / "data"
    rows = {s: load_rows(base / f"{s}-00000-of-00001.parquet") for s in ("train", "eval", "test")}
    kinds: dict[tuple[str, str], dict[str, str]] = defaultdict(dict)
    for split_rows in rows.values():
        for r in split_rows:
            kinds[(r["source"]["repo"], r["path"])][r["name"]] = r["kind"]

    files: dict[tuple[str, str], dict[str, list[tuple[int, str, str]]]] = defaultdict(dict)
    for d in load_rows(DATASETS_ROOT / "agda-decls" / "data" / "train-00000-of-00001.parquet"):
        sig = (d["declaration"] or {}).get("signature")
        if sig:
            files[(d["source"]["repo"], d["path"])].setdefault(d["name"], []).append(
                (sig["start"]["line"], d.get("signature") or "", d.get("body") or "")
            )

    def uses(key, name, line) -> list[tuple[str, int]]:
        decls = files[key]
        sig, body = next(((s, b) for l, s, b in decls.get(name, []) if l == line), ("", ""))
        found = []
        for word in set(WORD_RE.findall(body)) - set(WORD_RE.findall(sig)) - {name}:
            lines = [l for l, _, _ in decls.get(word, []) if l < line]
            if len(lines) == 1 and kinds[key].get(word) in LEMMA_KINDS:
                found.append((word, lines[0]))
        return found

    by_repo: dict[str, list[dict]] = defaultdict(list)
    for r in rows["test"]:
        decl = r["declaration"] or {}
        key = (r["source"]["repo"], r["path"])
        if (r["kind"] not in LEMMA_KINDS or decl.get("kind") != "type-signature"
                or set(decl.get("flags") or []) & SKIPPED_FLAGS
                or len(files[key].get(r["name"], [])) != 1):
            continue
        line = files[key][r["name"]][0][0]
        deepest, seen, frontier = 0, set(), [(r["name"], line, 0)]
        while frontier:
            name, at, d = frontier.pop()
            for used, used_line in uses(key, name, at):
                if used not in seen and d < depth:
                    seen.add(used)
                    deepest = max(deepest, d + 1)
                    frontier.append((used, used_line, d + 1))
        if deepest >= depth:
            by_repo[key[0]].append({
                "repo": key[0], "commit": r["source"]["commit"],
                "include": r["source"]["include"] or "src", "path": r["path"],
                "name": r["name"], "line": line, "signature": r["signature"],
                "definition": r["definition"], "prompt": r["prompt"],
            })

    rng = random.Random(seed)
    for items in by_repo.values():
        rng.shuffle(items)
    interleaved = [
        item for row in itertools.zip_longest(*by_repo.values()) for item in row if item is not None
    ]
    declarations = {
        key: {name: [l for l, _, _ in entries] for name, entries in decls.items()}
        for key, decls in files.items()
    }
    return interleaved, kinds, declarations


def build(
    item: dict,
    kinds: dict[str, str],
    declarations: dict[str, list[int]],
    depth: int,
    max_collateral: int,
    checkouts: str,
):
    """(the item with its tree and levels, or None; the reason it was not kept)."""

    root = checkout_for(item["repo"], item["commit"], Path(checkouts))

    with mirrored(root, item["path"]) as tree:
        agda_file = tree / item["path"]
        import_path = str(tree / item["include"].rstrip("/"))
        name = item["name"]

        nodes = lemma_tree(
            agda_file, name, item["line"], import_path, max_depth=depth,
            is_lemma=lambda n: kinds.get(n) in LEMMA_KINDS, timeout=AGDA_TIMEOUT,
        )

        if max(n.depth for n in nodes.values()) < depth:
            return None, "tree too shallow"
        if all(n.trivial for n in nodes.values() if n.depth == 1):
            return None, "direct lemmas trivial"

        source = agda_file.read_text()
        theorem_line = nodes[name].line
        levels: dict[str, dict] = {}

        for k in range(1, depth + 1):
            hidden = {n.name: n.line for n in nodes.values() if 1 <= n.depth <= k}
            removed = _with_dependents(source, declarations, hidden, theorem_line)
            if len(removed) - len(hidden) > max_collateral:
                return None, f"level {k}: too much collateral"
            if name in removed:
                return None, f"level {k}: theorem depends on a hidden lemma's dependents"

            # A declaration ends where the text parser says, but never past the
            # line before the file's next declaration (by agda-decls' lines).
            starts = sorted(l for lines in declarations.values() for l in lines)
            source_lines = source.splitlines()
            hide = []
            for n, at in removed.items():
                start, _, end, _ = declaration_span(source, n, at)
                first = source.count("\n", 0, start) + 1
                last = source.count("\n", 0, end) + 1
                following = [l for l in starts if l > first]
                if following:
                    last = min(last, following[0] - 1)
                # never across a literate file's code fence
                fences = [i for i in range(first, last + 1) if source_lines[i - 1].lstrip().startswith("```")]
                if fences:
                    last = fences[0] - 1
                hide.append([first, last])
            if any(first <= theorem_line <= last for first, last in hide):
                return None, f"level {k}: a hidden span reaches the theorem"

            problem = _check_hidden(agda_file, name, theorem_line, hide, sorted(hidden), import_path)
            if problem:
                return None, f"level {k}: {problem}"

            levels[str(k)] = {
                "hide": sorted(hide),
                "names": sorted(removed),
                "hidden": sorted(hidden),
                "statements": {n: nodes[n].normal for n in hidden},
            }

        if any(set(levels[str(k)]["hidden"]) <= set(levels[str(k - 1)]["hidden"]) for k in range(2, depth + 1)):
            return None, "deeper level hides nothing more"

    return {**item, "tree": {n: dataclasses.asdict(v) for n, v in nodes.items()}, "levels": levels}, None


def _with_dependents(
    source: str, declarations: dict[str, list[int]], hidden: dict[str, int], theorem_line: int
) -> dict[str, int]:
    """
    `hidden` and every declaration between them and the theorem that uses
    them, transitively. `declarations` are the file's own (from agda-decls),
    so names local to a `where` block are not taken for declarations.
    """

    removed = dict(hidden)
    first = min(hidden.values())
    between = [
        (n, at) for n, lines in declarations.items() for at in lines
        if first < at < theorem_line and n not in hidden
    ]
    texts = {}
    for n, at in between:
        try:
            start, _, end, _ = declaration_span(source, n, at)
            texts[(n, at)] = set(WORD_RE.findall(source[start:end]))
        except ValueError:
            continue

    changed = True
    while changed:
        changed = False
        for (n, at), words in texts.items():
            if n not in removed and words & set(removed):
                removed[n] = at
                changed = True

    return removed


def _check_hidden(
    agda_file: Path, name: str, line: int, hide: list[list[int]], hidden: list[str], import_path: str
) -> str:
    """Why hiding these lines does not work, or "" when it does."""

    with preserved_file(agda_file):
        Layout(agda_file, name, line, [tuple(r) for r in hide])
        check = check_sketch(agda_file, import_path=import_path, with_context=False, timeout=AGDA_TIMEOUT)
        if check.kind != "holes":
            message = " ".join(check.message.split())[:120]
            return f"does not load once hidden ({check.kind}): {message}"

        with AgdaSession(agda_file, import_path=import_path, timeout=AGDA_TIMEOUT) as session:
            load = session.load()
            goal = load.goals[0].id if load.goals else None
            if goal is None:
                return "no hole to check scope at"
            leaked = [n for n in hidden if where_defined(session, goal, n) is not None]
            if leaked:
                return f"still in scope: {', '.join(leaked)}"

    return ""


if __name__ == "__main__":
    raise SystemExit(main())
