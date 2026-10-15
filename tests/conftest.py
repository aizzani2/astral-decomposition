"""
Shared fixtures. Tests that need Agda work in a copy of a small Agda project
(tests/agda: an .agda-lib and a Base module), so the pipeline sees the same
kind of tree a library checkout gives it, and are skipped when no Agda is on
PATH.
"""

from __future__ import annotations

import shutil
from pathlib import Path

import pytest

FIXTURE = Path(__file__).parent / "agda"

needs_agda = pytest.mark.skipif(shutil.which("agda") is None, reason="no Agda on PATH")


@pytest.fixture
def project(tmp_path: Path) -> Path:
    """A private copy of the fixture project."""

    root = tmp_path / "project"
    shutil.copytree(FIXTURE, root, ignore=shutil.ignore_patterns("_build", "*.agdai"))
    return root


def write_target(root: Path, body: str, name: str = "Target") -> Path:
    """A module in the project importing Base."""

    path = root / f"{name}.agda"
    path.write_text(f"module {name} where\n\nopen import Base\n\n" + body.strip() + "\n")
    return path
