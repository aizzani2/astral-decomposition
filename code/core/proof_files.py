from pathlib import Path

from util.helper_utils import helper_signatures_to_text
from core.proof_state import ProofObligation, ProposedHelper


DEFAULT_HELPERS_MODULE = """module Tests.Helpers where

open import Tests.Context
"""


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


def reset_helpers_file(helpers_file: Path) -> None:
    helpers_file.write_text(DEFAULT_HELPERS_MODULE)


def write_postulated_helpers_file(
    helpers_file: Path,
    helpers: list[ProposedHelper | ProofObligation],
) -> None:
    helper_text = helper_signatures_to_text(helpers)

    helpers_file.write_text(
        f"""module Tests.Helpers where

open import Tests.Context

postulate
{_indent_block(helper_text, spaces=2)}
"""
    )


def write_helper_goal_file(
    helper_goal_file: Path,
    obligation: ProofObligation,
    imports: list[str] | None = None,
) -> None:
    """
    Write a temporary Agda file containing exactly one helper goal.

    The helper goal may import Tests.Helpers, which should contain only
    already-proved helpers during recursive proof.
    """

    if imports is None:
        imports = [
            "open import Tests.Context",
            "open import Tests.Helpers",
        ]

    imports_text = "\n".join(imports)

    helper_goal_file.write_text(
        f"""module Tests.HelperGoal where

{imports_text}

{obligation.name} : {obligation.signature}
{obligation.name} = {{!!}}
"""
    )


def write_final_helpers_file(
    helpers_file: Path,
    helper_declarations: list[str],
) -> None:
    declarations_text = "\n\n".join(
        declaration.strip()
        for declaration in helper_declarations
        if declaration.strip()
    )

    helpers_file.write_text(
        f"""module Tests.Helpers where

open import Tests.Context

{declarations_text}
"""
    )


def append_helper_declaration(
    helpers_file: Path,
    declaration: str,
) -> None:
    current = helpers_file.read_text() if helpers_file.exists() else DEFAULT_HELPERS_MODULE

    if not current.endswith("\n"):
        current += "\n"

    helpers_file.write_text(current + "\n" + declaration.strip() + "\n")


def _indent_block(text: str, spaces: int) -> str:
    prefix = " " * spaces

    return "\n".join(
        prefix + line if line.strip() else line
        for line in text.splitlines()
    )