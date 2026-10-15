from pathlib import Path
from contextlib import contextmanager
from typing import Iterator


def save_file(path: Path) -> str | None:
    if not path.exists():
        return None

    return path.read_text()


def restore_file(path: Path, content: str | None) -> None:
    if content is None:
        if path.exists():
            path.unlink()
    else:
        path.write_text(content)

@contextmanager
def preserved_file(path: Path) -> Iterator[str | None]:
    """Restore path's contents on the way out, including on Ctrl-C."""
    original = save_file(path)
    try:
        yield original
    finally:
        restore_file(path, original)
