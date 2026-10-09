"""
The astral-expmath Agda datasets, as rows deproof can work on.

Two Hugging Face datasets built by astral-autoformalizer
(github.com/kfish610/astral-autoformalizer, `confs/data/*.yaml`):

    agda-decls               every declaration of each pinned checkout, with
                             the compiler's own ranges (a modified Agda dumps
                             them while scope checking)
    agda-informalize-stdlib  stdlib declarations with an LLM-written informal
                             statement and, for lemmas and theorems, an
                             informal proof; no ranges

`load_rows` reads a downloaded parquet file; `join_informal` attaches the
ranges from agda-decls to the informal rows (the join their README describes:
repo, path, name, with keys more than one row answers to dropped); and
`checkout_for` finds the local checkout of a row's pinned commit.

Download with `hf download --repo-type dataset astral-expmath/<name>`.
Reading parquet needs pyarrow: `pip install -e '.[data]'`.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from pathlib import Path

from core.config import CHECKOUTS_ROOT

# The commits the datasets were built from, and the stdlib the other two
# libraries depend on (their .agda-lib says standard-library-2.3).
PINNED = {
    "agda/agda-stdlib": "47beb938489d1d9dd27c93c828a4e5e161acf758",
    "agda/agda-categories": "fbd1259c2dcf011ee1936fa8c24a1b10e6285673",
    "ualib/agda-algebras": "c56c89b378cca966aaaf2a3f2cda7861729577a0",
}
STDLIB_2_3 = ("agda-stdlib-2.3", "v2.3")


@dataclass
class DatasetDecl:
    """One declaration from the datasets, with where it lives."""

    repo: str
    commit: str
    include: str          # include directory, relative to the checkout
    path: str             # file, relative to the checkout
    name: str
    scope: str
    line: int             # 1-based line of its signature, from agda-decls
    signature: str
    definition: str
    kind: str = ""        # informal classification: lemma, theorem, definition, ...
    statement: str = ""   # informal statement
    informal_proof: str = ""

    @property
    def id(self) -> str:
        return f"{self.repo}:{self.path}:{self.line}:{self.name}"


def load_rows(parquet: Path | str) -> list[dict]:
    try:
        import pyarrow.parquet as pq
    except ImportError as error:
        raise RuntimeError(
            "Reading the datasets needs pyarrow: pip install -e '.[data]'"
        ) from error

    return pq.read_table(str(parquet)).to_pylist()


def _repo(source: dict) -> str:
    return source.get("repo") or source.get("name") or ""


def join_informal(informal_rows: list[dict], decl_rows: list[dict]) -> list[DatasetDecl]:
    """
    Informal rows with their compiler ranges. A key (repo, path, name) that
    several declarations answer to is resolved by scope, and dropped if that
    still leaves more than one.
    """

    by_key: dict[tuple[str, str, str], list[dict]] = {}

    for row in decl_rows:
        key = (_repo(row["source"]), row["path"], row["name"])
        by_key.setdefault(key, []).append(row)

    out: list[DatasetDecl] = []

    for row in informal_rows:
        key = (_repo(row["source"]), row["path"], row["name"])
        matches = by_key.get(key, [])

        if len(matches) > 1:
            matches = [m for m in matches if m.get("scope") == row.get("scope")]

        if len(matches) != 1:
            continue

        decl = matches[0]
        source = decl["source"]

        out.append(DatasetDecl(
            repo=key[0],
            commit=source.get("commit") or "",
            include=source.get("include") or "src",
            path=row["path"],
            name=row["name"],
            scope=row.get("scope") or "",
            line=decl["declaration"]["signature"]["start"]["line"],
            signature=row.get("signature") or decl.get("signature") or "",
            definition=row.get("definition") or decl.get("body") or "",
            kind=row.get("kind") or "",
            statement=row.get("statement") or "",
            informal_proof=row.get("informal_proof") or "",
        ))

    return out


def checkout_for(repo: str, commit: str, root: Path = CHECKOUTS_ROOT) -> Path:
    """
    The local checkout of `repo`, which must be at `commit`: a declaration's
    line numbers are only right in the snapshot the dataset was built from.
    """

    path = root / repo.split("/")[-1]

    if not path.is_dir():
        raise FileNotFoundError(
            f"No checkout of {repo} at {path}. Clone it at {commit}, or set ASTRAL_CHECKOUTS."
        )

    if commit:
        head = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            capture_output=True, text=True, check=False,
        ).stdout.strip()

        if head != commit:
            raise ValueError(f"{path} is at {head or 'no commit'}, the dataset pins {commit}.")

    return path
