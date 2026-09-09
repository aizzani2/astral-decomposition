from pathlib import Path
from contextlib import contextmanager
from typing import Iterator


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

@contextmanager
def preserved_file(path: Path) -> Iterator[str | None]:
    """Restore path's contents on the way out, including on Ctrl-C."""
    original = save_file(path)
    try:
        yield original
    finally:
        restore_file(path, original)

def reset_helpers_file(helpers_file: Path) -> None:
    helpers_file.parent.mkdir(parents=True, exist_ok=True)
    helpers_file.write_text(DEFAULT_HELPERS_MODULE)


def write_postulated_helpers_file(
    helpers_file: Path,
    helpers: list[ProposedHelper | ProofObligation],
) -> None:
    """
    Write the helpers module with every helper as a postulate.

    Postulates are how a sketch's assumptions get typechecked before they are
    proved. Anything left postulated at the end of a run is an unproved
    assumption, so the final check must reject a helpers file that still
    contains this keyword.
    """

    helpers_file.parent.mkdir(parents=True, exist_ok=True)

    if not helpers:
        reset_helpers_file(helpers_file)
        return

    lines: list[str] = []

    for helper in helpers:
        hint = getattr(helper, "informal_hint", "")

        if hint:
            lines.append(f"  -- {hint}")

        lines.append(f"  {helper.name} : {helper.signature}")

    body = "\n".join(lines)

    helpers_file.write_text(
        f"""module Tests.Helpers where

open import Tests.Context

postulate
{body}
"""
    )


def write_helper_goal_file(
    helper_goal_file: Path,
    obligation: ProofObligation,
    imports: list[str] | None = None,
) -> None:
    """
    Write a temporary Agda file containing exactly one helper goal.

    Tests.Helpers should contain only already-proved helpers at this point, so
    that a lemma cannot be proved from an assumption that is itself unproved.
    """

    if imports is None:
        imports = [
            "open import Tests.Context",
            "open import Tests.Helpers",
        ]

    imports_text = "\n".join(imports)
    comment = f"-- {obligation.informal_hint}\n" if obligation.informal_hint else ""

    helper_goal_file.parent.mkdir(parents=True, exist_ok=True)
    helper_goal_file.write_text(
        f"""module Tests.HelperGoal where

{imports_text}

{comment}{obligation.name} : {obligation.signature}
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
    current = (
        helpers_file.read_text() if helpers_file.exists() else DEFAULT_HELPERS_MODULE
    )

    if not current.endswith("\n"):
        current += "\n"

    helpers_file.write_text(current + "\n" + declaration.strip() + "\n")


def helpers_are_fully_proved(helpers_file: Path) -> bool:
    """No postulates left means no unproved assumptions are being relied on."""

    if not helpers_file.exists():
        return True

    return "postulate" not in helpers_file.read_text()


def postulate_block(helpers: list[ProposedHelper | ProofObligation]) -> str:
    """A `postulate` block declaring each helper, with its informal hint."""

    lines: list[str] = ["postulate"]

    for helper in helpers:
        hint = getattr(helper, "informal_hint", "")

        if hint:
            lines.append(f"  -- {hint}")

        lines.append(f"  {helper.name} : {helper.signature}")

    return "\n".join(lines)


def append_postulates(
    helpers_file: Path,
    helpers: list[ProposedHelper | ProofObligation],
) -> None:
    """
    Add postulates for `helpers` *without* discarding what is already in the
    helpers module. Overwriting was a real bug: a nested lemma's sketch used to
    wipe the sibling lemmas its parent had already proved and appended.
    """

    if not helpers:
        return

    append_helper_declaration(helpers_file, postulate_block(helpers))
