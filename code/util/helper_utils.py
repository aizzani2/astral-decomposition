from core.proof_state import ProofObligation, ProposedHelper


def parse_helper_signatures(helpers: str) -> list[ProposedHelper]:
    parsed: list[ProposedHelper] = []

    for line in helpers.strip().splitlines():
        line = line.strip()

        if not line:
            continue

        if line.startswith("--"):
            continue

        if line == "postulate":
            continue

        if "=" in line:
            continue

        if " : " not in line:
            continue

        name, signature = line.split(" : ", 1)
        name = name.strip()
        signature = signature.strip()

        if name and signature:
            parsed.append(ProposedHelper(name=name, signature=signature))

    if not parsed:
        raise ValueError("No valid helper signatures found.")

    return parsed


def proposed_helpers_to_obligations(
    helpers: list[ProposedHelper],
) -> list[ProofObligation]:
    return [
        ProofObligation(
            name=helper.name,
            signature=helper.signature,
        )
        for helper in helpers
    ]


def helper_signatures_to_text(helpers: list[ProposedHelper | ProofObligation]) -> str:
    return "\n".join(f"{helper.name} : {helper.signature}" for helper in helpers)


def indent_postulates_from_text(helpers: str) -> str:
    parsed = parse_helper_signatures(helpers)

    return "\n".join(
        f"  {helper.name} : {helper.signature}"
        for helper in parsed
    )