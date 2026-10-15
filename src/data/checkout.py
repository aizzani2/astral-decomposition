"""
Working on a file of a library checkout without writing into the checkout.

deproof loads a declaration's file with holes in it. Doing that in place would
leave a library checkout (agda-stdlib, a dataset's pinned snapshot) briefly
broken and would overwrite the module's cached interface. Instead the checkout
is mirrored as a tree of symlinks in a temporary directory, with real copies
of just the file being edited and of the directories its interface is written
to, so Agda reads every other module's interface from the checkout and writes
nothing back.

Adapted from `AgdaClient.check` in astral-autoformalizer
(src/astral/autoformalizer/util/agda/client.py).
"""

from __future__ import annotations

from contextlib import contextmanager
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import Iterator


def _break_symlink_chain(temp_root: Path, rel_path: Path) -> Path:
    """
    Make every directory on the way to `rel_path` a real directory (whose
    entries still link into the checkout), so `rel_path` itself can be a real
    file. Returns the path, with any symlink at the leaf removed.
    """

    current = temp_root

    for part in rel_path.parent.parts:
        current = current / part

        if current.is_symlink():
            target = current.resolve()
            current.unlink()
            current.mkdir()

            for entry in target.iterdir():
                (current / entry.name).symlink_to(entry)

    dest = current / rel_path.name

    if dest.is_symlink():
        dest.unlink()

    return dest


def _project(root: Path, rel_path: Path) -> Path:
    """The file's Agda project root: its nearest `.agda-lib`, under `root`."""

    directory = (root / rel_path).parent

    while directory != root and not any(directory.glob("*.agda-lib")):
        directory = directory.parent

    return directory.relative_to(root)


def _interfaces(root: Path, rel_path: Path) -> list[Path]:
    """Where each Agda version caches the file's interface, relative to `root`."""

    project = _project(root, rel_path)
    local = rel_path.relative_to(project).parent / f"{rel_path.name.split('.')[0]}.agdai"

    return [
        build.relative_to(root) / local
        for build in (root / project).glob("_build/*/agda")
    ]


@contextmanager
def mirrored(root: Path, rel_path: Path | str) -> Iterator[Path]:
    """
    Yield the mirror's root; `<mirror>/<rel_path>` is a real, writable copy of
    the checkout's file, and everything else links into the checkout.

        with mirrored(stdlib, "src/Data/Nat/Properties.agda") as tree:
            decompose(tree / "src/Data/Nat/Properties.agda", "+-comm",
                      import_path=str(tree / "src"))
    """

    root = root.resolve()
    rel_path = Path(rel_path)

    with TemporaryDirectory(prefix="deproof-") as temp_dir:
        temp_root = Path(temp_dir)

        for entry in root.iterdir():
            (temp_root / entry.name).symlink_to(entry)

        dest = _break_symlink_chain(temp_root, rel_path)
        dest.write_text((root / rel_path).read_text(encoding="utf-8"), encoding="utf-8")

        # The edited module's interface is written into the mirror, never the
        # checkout's _build.
        for interface in _interfaces(root, rel_path):
            _break_symlink_chain(temp_root, interface)

        yield temp_root
