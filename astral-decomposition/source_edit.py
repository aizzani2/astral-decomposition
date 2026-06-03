import re


def ensure_import(source: str, import_line: str) -> str:
    """
    Ensure that source contains import_line.

    If the import already exists, return source unchanged.
    Otherwise, insert it after the module declaration and existing imports.
    """

    if import_line in source.splitlines():
        return source

    lines = source.splitlines()

    insert_at = 0

    for index, line in enumerate(lines):
        stripped = line.strip()

        if stripped.startswith("module "):
            insert_at = index + 1
            continue

        if stripped.startswith("open import ") or stripped.startswith("import "):
            insert_at = index + 1
            continue

        if not stripped:
            continue

        if insert_at > 0:
            break

    lines.insert(insert_at, import_line)

    return "\n".join(lines) + "\n"


def validate_declaration_name(declaration: str, expected_name: str) -> None:
    """
    Check that the first non-empty line of declaration is the signature
    for expected_name.
    """

    first_line = _first_nonempty_line(declaration)

    if first_line is None:
        raise ValueError("Declaration is empty.")

    actual_name = _declaration_name_from_signature(first_line)

    if actual_name != expected_name:
        raise ValueError(
            "The declaration has the wrong name.\n"
            f"Expected: {expected_name}\n"
            f"Got:      {actual_name}\n"
            f"First line: {first_line}"
        )


def replace_top_level_decl(source: str, name: str, replacement: str) -> str:
    """
    Replace the full top-level declaration named `name`.

    This assumes the declaration starts with a top-level signature line:

        name : ...

    and continues until the next non-empty top-level signature line.
    """

    lines = source.splitlines()
    start = _find_top_level_signature_index(lines, name)

    end = len(lines)

    for index in range(start + 1, len(lines)):
        line = lines[index]

        if _is_top_level_signature_line(line):
            end = index
            break

    new_lines = (
        lines[:start]
        + replacement.strip().splitlines()
        + lines[end:]
    )

    return "\n".join(new_lines) + "\n"


def _find_top_level_signature_index(lines: list[str], name: str) -> int:
    expected_prefix = f"{name} :"

    for index, line in enumerate(lines):
        if line.startswith(expected_prefix):
            return index

    raise ValueError(f"Could not find top-level declaration signature for {name}.")


def _is_top_level_signature_line(line: str) -> bool:
    if not line:
        return False

    if line.startswith(" ") or line.startswith("\t"):
        return False

    if line.startswith("--"):
        return False

    return " : " in line


def _first_nonempty_line(text: str) -> str | None:
    for line in text.splitlines():
        stripped = line.strip()

        if stripped:
            return stripped

    return None


def _declaration_name_from_signature(signature_line: str) -> str:
    if " : " not in signature_line:
        raise ValueError(
            "Expected declaration to start with a type signature, "
            f"but got:\n{signature_line}"
        )

    name, _rest = signature_line.split(" : ", 1)
    name = name.strip()

    if not name:
        raise ValueError(f"Could not parse declaration name from: {signature_line}")

    return name