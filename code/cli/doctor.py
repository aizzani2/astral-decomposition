"""
Check that everything a library run needs is in place.

    python cli/doctor.py [--model claude-sonnet-5-5 | --model qwen3.5:4b --base-url URL]

Checks `agda` (the library snapshots need 2.8), that the standard library
agda-categories and agda-algebras depend on (standard-library-2.3) is
registered in Agda's libraries file, each checkout at the commit the datasets
pin, the downloaded datasets, pyarrow, and that the model is reachable.
Prints one line per check and exits 1 if any failed.
"""

from __future__ import annotations

import argparse
import subprocess
from pathlib import Path

import requests

from core import config
from util.agda_data import PINNED, STDLIB_2_3

DATASETS = ("agda-decls", "agda-informalize-stdlib", "agda-autoformalize-context")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--model", default=config.DEFAULT_MODEL, help="Ollama tag or Claude id.")
    parser.add_argument("--base-url", default=config.OLLAMA_BASE_URL)
    args = parser.parse_args(argv)

    checks = [
        check_agda(),
        check_dependency_library(),
        *[check_checkout(repo.split("/")[-1], commit) for repo, commit in PINNED.items()],
        check_checkout(STDLIB_2_3[0], None),
        *[check_dataset(name) for name in DATASETS],
        check_import("pyarrow", "pip install -e '.[data]'"),
        check_model(args.model, args.base_url),
    ]

    for ok, label, detail in checks:
        print(f"{'ok  ' if ok else 'FAIL'}  {label:<34} {detail}")

    return 0 if all(ok for ok, _, _ in checks) else 1


def check_agda() -> tuple[bool, str, str]:
    try:
        out = subprocess.run(["agda", "--version"], capture_output=True, text=True, timeout=10).stdout
    except OSError as error:
        return False, "agda", str(error)

    version = out.split("version", 1)[-1].split()[0] if "version" in out else "?"
    ok = tuple(int(p) for p in version.split(".")[:2] if p.isdigit()) >= (2, 8)
    return ok, "agda", version + ("" if ok else "  (library runs need 2.8)")


def check_dependency_library() -> tuple[bool, str, str]:
    """standard-library-2.3 in the libraries file Agda 2.8 reads."""

    label = f"{STDLIB_2_3[0]} registered"
    try:
        app_dir = Path(subprocess.run(["agda", "--print-agda-app-dir"], capture_output=True,
                                      text=True, timeout=10).stdout.strip())
    except OSError as error:
        return False, label, str(error)

    files = [app_dir / "libraries-2.8.0", app_dir / "libraries"]
    listed = [line.strip() for f in files if f.exists() for line in f.read_text().splitlines()]
    wanted = config.CHECKOUTS_ROOT / STDLIB_2_3[0] / "standard-library.agda-lib"
    ok = any(Path(line).expanduser().resolve() == wanted.resolve() for line in listed if line)
    return ok, label, (str(files[0]) if ok else f"add {wanted} to {files[0]}")


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


def check_model(model: str, url: str) -> tuple[bool, str, str]:
    if model.startswith("claude"):
        return check_import("anthropic", "pip install -e '.[claude]'")

    role = "model"
    try:
        tags = requests.get(f"{url.rstrip('/')}/api/tags", timeout=5).json()
    except Exception as error:
        return False, f"{role} ({url})", f"not reachable: {type(error).__name__}"
    names = [m.get("name", "") for m in tags.get("models", [])]
    ok = any(n == model or n.split(":")[0] == model for n in names)
    return ok, f"{role} ({url})", model if ok else f"{model} not served (has {len(names)} models)"


if __name__ == "__main__":
    raise SystemExit(main())
