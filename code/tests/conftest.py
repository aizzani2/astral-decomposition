"""
Shared fixtures. Tests that need Agda use the toy tree (agda_files/Tests),
copied into a temporary directory so the repository copy is never touched,
and are skipped when no Agda is on PATH.
"""

from __future__ import annotations

import shutil
from pathlib import Path

import pytest

from core import config
from core.config import AGDA_ROOT

needs_agda = pytest.mark.skipif(shutil.which(config.AGDA_BIN) is None, reason="no Agda on PATH")


@pytest.fixture
def toy_tree(tmp_path: Path) -> Path:
    """A private copy of agda_files/ with an empty Helpers module."""

    root = tmp_path / "agda_files"
    shutil.copytree(AGDA_ROOT, root, ignore=shutil.ignore_patterns("*.agdai", "_build"))
    (root / "Tests" / "Helpers.agda").write_text(
        "module Tests.Helpers where\n\nopen import Tests.Context\n"
    )
    return root


def write_target(root: Path, body: str, name: str = "Target") -> Path:
    """A module in the toy tree importing the test context."""

    path = root / "Tests" / f"{name}.agda"
    path.write_text(
        f"module Tests.{name} where\n\n"
        "open import Tests.Util\nopen import Tests.Helpers\nopen import Tests.Context\n\n"
        + body.strip() + "\n"
    )
    return path
