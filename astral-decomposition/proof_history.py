from dataclasses import dataclass, field


@dataclass
class ProofAttempt:
    phase: str
    target_name: str
    candidate: str
    agda_output: str


@dataclass
class ProofHistory:
    attempts: list[ProofAttempt] = field(default_factory=list)

    def add(
        self,
        phase: str,
        target_name: str,
        candidate: str,
        agda_output: str,
    ) -> None:
        self.attempts.append(
            ProofAttempt(
                phase=phase,
                target_name=target_name,
                candidate=candidate,
                agda_output=agda_output,
            )
        )

    def messages_for_target(self, target_name: str) -> list[str]:
        messages: list[str] = []

        for attempt in self.attempts:
            if attempt.target_name != target_name:
                continue

            messages.append(
                f"""
Phase: {attempt.phase}

Candidate:
{attempt.candidate}

Agda output:
{truncate_error(attempt.agda_output)}
"""
            )

        return messages


def truncate_error(output: str, max_chars: int = 4000) -> str:
    if len(output) <= max_chars:
        return output

    return output[:max_chars] + "\n\n... truncated ..."