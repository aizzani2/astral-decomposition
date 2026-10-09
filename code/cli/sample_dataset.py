"""
Draw a sample of library theorems for cli/run_dsp_dataset.py.

    python cli/sample_dataset.py --per-repo 8 --chains 4 --seed 11 --out samples/test24.json

Theorems come from the held-out test split of agda-autoformalize-context, so
the formalizer has not been trained on them, and each comes with its prompt
(file, header, context, informal statement). Per repo it keeps lemmas and
theorems whose proof is at most `--max-lines` long and not a constructor,
field, postulate and so on, and takes `--chains` whose proof is an equational
chain (`begin ... ∎`) and the rest from the others.

The ablation runs under runs/*ablation-* used --per-repo 8 --chains 4 --seed 11.
"""

from __future__ import annotations

import argparse
import json
import random
import re
import sys
from pathlib import Path

from core.config import DATASETS_ROOT
from util.agda_data import PINNED, load_rows

SKIPPED_FLAGS = {"constructor", "generalize", "postulate", "field", "instance", "abstract"}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--split", default=str(
        DATASETS_ROOT / "agda-autoformalize-context" / "data" / "test-00000-of-00001.parquet"))
    parser.add_argument("--per-repo", type=int, default=8)
    parser.add_argument("--chains", type=int, default=4, help="Of those, equational chains.")
    parser.add_argument("--max-lines", type=int, default=20)
    parser.add_argument("--seed", type=int, default=11)
    parser.add_argument("--out", required=True)
    args = parser.parse_args(argv)

    rows = load_rows(args.split)
    rng = random.Random(args.seed)
    sample: list[dict] = []

    for repo in PINNED:
        chain, plain = [], []

        for row in rows:
            item = _item(row, repo, args.max_lines)
            if item is not None:
                (chain if re.search(r"\bbegin\b", item["definition"]) else plain).append(item)

        rng.shuffle(chain)
        rng.shuffle(plain)
        k = min(args.chains, len(chain))
        sample += chain[:k] + plain[: args.per_repo - k]
        print(f"{repo}: {len(chain)} chains, {len(plain)} others in the split", file=sys.stderr)

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(sample, indent=1, ensure_ascii=False))
    print(f"{len(sample)} theorems -> {out}", file=sys.stderr)
    return 0


def _item(row: dict, repo: str, max_lines: int) -> dict | None:
    decl = row["declaration"]
    body = (row["definition"] or "").strip()

    if (row["source"]["repo"] != repo or row["kind"] not in ("lemma", "theorem")
            or decl["kind"] != "type-signature" or not body
            or len(body.splitlines()) > max_lines or set(decl["flags"]) & SKIPPED_FLAGS):
        return None

    return {
        "repo": repo, "commit": row["source"]["commit"],
        "include": row["source"]["include"] or "src",
        "path": row["path"], "name": row["name"], "line": decl["signature"]["start"]["line"],
        "signature": row["signature"], "definition": row["definition"], "prompt": row["prompt"],
    }


if __name__ == "__main__":
    raise SystemExit(main())
