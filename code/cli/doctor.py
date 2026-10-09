"""
Check that everything a library run needs is in place.

    python cli/doctor.py [--model qwen3.5:4b --base-url http://localhost:11435]
                         [--formalizer ... --formalizer-url ...] [--write-library-file]

Checks the Agda binary (the library snapshots need 2.8), the Agda library
file and the libraries it lists, each checkout at the commit the datasets pin,
the downloaded datasets, pyarrow, and that the drafting and formalizing
models are served. Prints one line per check and exits 1 if any failed.
`--write-library-file` (re)writes the library file from the checkouts.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

import requests

from core import config
from util.agda_data import PINNED, STDLIB_2_3

DATASETS = ("agda-decls", "agda-informalize-stdlib", "agda-autoformalize-context")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--model", default=config.DEFAULT_MODEL, help="The drafting model.")
    parser.add_argument("--base-url", default=config.OLLAMA_BASE_URL)
    parser.add_argument("--formalizer", default=config.FORMALIZER_MODEL)
    parser.add_argument("--formalizer-url", default=config.FORMALIZER_URL)
    parser.add_argument("--write-library-file", action="store_true")
    args = parser.parse_args(argv)

    if args.write_library_file:
        write_library_file()

    checks = [
        check_agda(),
        check_library_file(),
        *[check_checkout(repo.split("/")[-1], commit) for repo, commit in PINNED.items()],
        check_checkout(STDLIB_2_3[0], None),
        *[check_dataset(name) for name in DATASETS],
        check_import("pyarrow", "pip install -e '.[data]'"),
        check_model("drafter", args.model, args.base_url),
        check_model("formalizer", args.formalizer, args.formalizer_url),
    ]

    for ok, label, detail in checks:
        print(f"{'ok  ' if ok else 'FAIL'}  {label:<34} {detail}")

    return 0 if all(ok for ok, _, _ in checks) else 1


def check_agda() -> tuple[bool, str, str]:
    try:
        out = subprocess.run([config.AGDA_BIN, "--version"], capture_output=True, text=True, timeout=10).stdout
    except OSError as error:
        return False, f"Agda ({config.AGDA_BIN})", str(error)

    version = out.split("version", 1)[-1].split()[0] if "version" in out else "?"
    ok = tuple(int(p) for p in version.split(".")[:2] if p.isdigit()) >= (2, 8)
    hint = "" if ok else "  (library runs need 2.8: set AGDA_BIN)"
    return ok, f"Agda ({config.AGDA_BIN})", version + hint


def check_library_file() -> tuple[bool, str, str]:
    path = config.AGDA_LIBRARY_FILE
    if not path.exists():
        return False, "Agda library file", f"{path} missing (--write-library-file)"
    missing = [l for l in path.read_text().split() if l and not Path(l).exists()]
    return not missing, "Agda library file", f"{path}" + (f"; missing: {', '.join(missing)}" if missing else "")


def check_checkout(name: str, commit: str | None) -> tuple[bool, str, str]:
    path = config.CHECKOUTS_ROOT / name
    if not path.is_dir():
        return False, f"checkout {name}", f"{path} missing"
    head = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"],
                          capture_output=True, text=True).stdout.strip()
    if commit and head != commit:
        return False, f"checkout {name}", f"at {head[:10]}, datasets pin {commit[:10]}"
    return True, f"checkout {name}", f"{path} @ {head[:10]}"


def check_dataset(name: str) -> tuple[bool, str, str]:
    path = config.DATASETS_ROOT / name / "data"
    files = sorted(path.glob("*.parquet")) if path.is_dir() else []
    return bool(files), f"dataset {name}", (f"{len(files)} parquet file(s)" if files else
                                            f"missing: hf download --repo-type dataset astral-expmath/{name} "
                                            f"--local-dir {config.DATASETS_ROOT / name}")


def check_import(module: str, hint: str) -> tuple[bool, str, str]:
    try:
        __import__(module)
        return True, module, "importable"
    except ImportError:
        return False, module, hint


def check_model(role: str, model: str, url: str) -> tuple[bool, str, str]:
    try:
        tags = requests.get(f"{url.rstrip('/')}/api/tags", timeout=5).json()
    except Exception as error:
        return False, f"{role} ({url})", f"not reachable: {type(error).__name__}"
    names = [m.get("name", "") for m in tags.get("models", [])]
    ok = any(n == model or n.split(":")[0] == model for n in names)
    return ok, f"{role} ({url})", model if ok else f"{model} not served (has {len(names)} models)"


def write_library_file() -> None:
    """The library file for Agda: the stdlib 2.3 the other libraries depend on, and them."""

    root = config.CHECKOUTS_ROOT
    libs = [root / STDLIB_2_3[0] / "standard-library.agda-lib"] + [
        lib for repo in PINNED if repo != "agda/agda-stdlib"
        for lib in sorted((root / repo.split("/")[-1]).glob("*.agda-lib"))
    ]
    config.AGDA_LIBRARY_FILE.write_text("\n".join(str(l) for l in libs) + "\n")
    print(f"wrote {config.AGDA_LIBRARY_FILE}", file=sys.stderr)


if __name__ == "__main__":
    raise SystemExit(main())
