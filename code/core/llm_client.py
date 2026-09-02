"""
LLM client for the Draft / Sketch / Prove pipeline.

Three model-facing operations, in the order the paper uses them:

    draft_informal_proof   informal statement            -> InformalProof
    sketch                 InformalProof + Agda context  -> FormalSketch text
    fill_gap               one goal type + context       -> one Agda term

Everything is transport-agnostic: `LLMBackend` is a one-method protocol, so
swapping Ollama for the autoformalizer (Kevin) or a hosted model is a
constructor argument, not a rewrite. Nothing below knows about HTTP.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Protocol

import requests

from core import prompts
from core.proof_state import (
    ContextEntry,
    InformalProof,
    InformalStep,
    LLMDeclResult,
    LLMHelperDeclResult,
    ProofObligation,
)


# ---------------------------------------------------------------------------
# Backends
# ---------------------------------------------------------------------------


class LLMBackend(Protocol):
    def generate(self, prompt: str, timeout: int = 180, stop: list[str] | None = None) -> str:
        ...


@dataclass
class OllamaBackend:
    model: str = "qwen2.5-coder:14b"
    base_url: str = "http://localhost:11434"
    temperature: float = 0.6
    top_p: float = 0.95

    def generate(self, prompt: str, timeout: int = 180, stop: list[str] | None = None) -> str:
        options: dict[str, object] = {
            "temperature": self.temperature,
            "top_p": self.top_p,
        }

        if stop:
            options["stop"] = stop

        response = requests.post(
            f"{self.base_url.rstrip('/')}/api/generate",
            json={
                "model": self.model,
                "prompt": prompt,
                "stream": False,
                "options": options,
            },
            timeout=timeout,
        )

        if response.status_code != 200:
            raise RuntimeError(
                f"Ollama returned {response.status_code}:\n{response.text}"
            )

        return response.json()["response"]


@dataclass
class EchoBackend:
    """Deterministic stub backend, for testing the harness without a model."""

    responses: list[str]
    calls: list[str] | None = None

    def generate(self, prompt: str, timeout: int = 180, stop: list[str] | None = None) -> str:
        if self.calls is None:
            self.calls = []

        self.calls.append(prompt)

        if not self.responses:
            raise RuntimeError("EchoBackend ran out of scripted responses.")

        return self.responses.pop(0)


# ---------------------------------------------------------------------------
# Client
# ---------------------------------------------------------------------------


class ProofLLM:
    """
    Stage-aware wrapper around a backend.

    Sampling note: the paper gets most of its mileage from *many* drafts rather
    than many sketches per draft (Figure 5, right). `draft_informal_proof` is
    therefore the place to spend a sampling budget; `n_samples` returns a list.
    """

    def __init__(
        self,
        backend: LLMBackend | None = None,
        model: str = "qwen2.5-coder:7b",
        base_url: str = "http://localhost:11434",
        timeout: int = 180,
    ) -> None:
        self.backend = backend or OllamaBackend(model=model, base_url=base_url)
        self.timeout = timeout

    # -- stage 1: draft ----------------------------------------------------

    def draft_informal_proof(
        self,
        informal_statement: str,
        formal_signature: str,
        extra_context: str = "",
    ) -> InformalProof:
        prompt = prompts.DRAFT_TEMPLATE.format(
            system=prompts.DRAFT_SYSTEM,
            few_shot=prompts.DRAFT_FEW_SHOT,
            informal_statement=informal_statement.strip(),
            formal_signature=formal_signature.strip(),
            extra_context=(extra_context + "\n") if extra_context else "",
        )

        raw = self.backend.generate(
            prompt,
            timeout=self.timeout,
            stop=["</INFORMAL_PROOF>"],
        )

        steps = parse_informal_steps(raw)

        return InformalProof(
            statement=informal_statement.strip(),
            steps=steps,
            raw=raw.strip(),
        )

    def draft_informal_proofs(
        self,
        informal_statement: str,
        formal_signature: str,
        n_samples: int = 1,
        extra_context: str = "",
    ) -> list[InformalProof]:
        drafts: list[InformalProof] = []

        for _ in range(n_samples):
            try:
                drafts.append(
                    self.draft_informal_proof(
                        informal_statement=informal_statement,
                        formal_signature=formal_signature,
                        extra_context=extra_context,
                    )
                )
            except ValueError:
                continue

        return drafts

    # -- stage 2: sketch ---------------------------------------------------

    def sketch(
        self,
        source: str,
        target_name: str,
        signature: str,
        informal: InformalProof,
        available_names: str = "",
        previous_errors: list[str] | None = None,
        helpers_module: str = "Tests.Helpers",
        context_module: str = "Tests.Context",
    ) -> tuple[list[ProofObligation], str, str]:
        """
        Returns (lemma obligations, sketch text with holes, raw response).
        """

        prompt = prompts.SKETCH_TEMPLATE.format(
            system=prompts.SKETCH_SYSTEM,
            few_shot=prompts.SKETCH_FEW_SHOT,
            informal_proof=informal.as_numbered_text(),
            signature=signature.strip(),
            available_names=available_names or "(none listed)",
            source=source,
            target_name=target_name,
            helpers_module=helpers_module,
            context_module=context_module,
            error_text=format_previous_errors(previous_errors or []),
        )

        raw = self.backend.generate(prompt, timeout=self.timeout)

        # The prompt ends with an open <AGDA_LEMMAS> tag, so the model's
        # continuation is the body. Re-attach it before parsing.
        text = "<AGDA_LEMMAS>" + raw if "<AGDA_LEMMAS>" not in raw else raw

        lemma_block = extract_between_tags(text, "AGDA_LEMMAS") or ""
        sketch = extract_between_tags(text, "AGDA_SKETCH")

        if sketch is None:
            sketch = strip_markdown_code_fences(text).strip()

        if not sketch.strip():
            raise ValueError("Model returned an empty <AGDA_SKETCH> block.")

        lemmas = parse_lemma_signatures(lemma_block, informal=informal)

        return lemmas, sketch.strip(), raw.strip()

    # -- stage 3: prove ----------------------------------------------------

    def fill_gap(
        self,
        goal_type: str,
        context: list[ContextEntry],
        informal_hint: str,
        excerpt: str,
        available_names: str = "",
        previous_errors: list[str] | None = None,
        target_name: str = ""
    ) -> str:
        prompt = prompts.GAP_TEMPLATE.format(
            goal_type=goal_type.strip(),
            context="\n".join(f"  {e.name} : {e.type}" for e in context) or "  (empty)",
            informal_hint=informal_hint.strip() or "(none recorded)",
            available_names=available_names or "(none listed)",
            excerpt=excerpt,
            error_text=format_previous_errors(previous_errors or []),
            target_name=target_name,
        )

        raw = self.backend.generate(prompt, timeout=self.timeout, stop=["</AGDA_TERM>"])
        text = "<AGDA_TERM>" + raw if "<AGDA_TERM>" not in raw else raw

        term = extract_between_tags(text, "AGDA_TERM")

        if term is None:
            term = strip_markdown_code_fences(raw)

        term = term.strip()

        if not term:
            raise ValueError("Model returned an empty term for the hole.")

        if "{!" in term:
            raise ValueError("Model returned a term that still contains a hole.")

        return term

    def lemma_signature_for_gap(
        self,
        lemma_name: str,
        goal_type: str,
        context: list[ContextEntry],
        context_module: str = "Tests.Context",
    ) -> str:
        prompt = prompts.LEMMA_FROM_GAP_TEMPLATE.format(
            lemma_name=lemma_name,
            goal_type=goal_type.strip(),
            context="\n".join(f"  {e.name} : {e.type}" for e in context) or "  (empty)",
            context_module=context_module,
        )

        raw = self.backend.generate(prompt, timeout=self.timeout, stop=["</AGDA_SIG>"])
        text = raw

        if "<AGDA_SIG>" in raw:
            text = extract_between_tags(raw, "AGDA_SIG") or raw

        first_line = next(
            (line.strip() for line in text.splitlines() if line.strip()),
            "",
        )

        if first_line.startswith(f"{lemma_name} :"):
            first_line = first_line.split(":", 1)[1]

        signature = first_line.strip()

        if not signature:
            raise ValueError("Model returned an empty lemma signature.")

        return signature

    # -- legacy single-shot paths (kept so run_direct/run_single still work) --

    def ask_for_direct_declaration(
        self,
        source: str,
        target_name: str,
        goal_type: str,
        previous_errors: list[str],
    ) -> str:
        return self.ask_for_declaration(
            source=source,
            target_name=target_name,
            goal_type=goal_type,
            previous_errors=previous_errors,
        ).declaration

    def ask_for_declaration(
        self,
        source: str,
        target_name: str,
        goal_type: str,
        previous_errors: list[str],
    ) -> LLMDeclResult:
        prompt = f"""\
You are an Agda proof assistant agent. Complete this declaration: {target_name}

Return the full replacement declaration inside <AGDA_DECL> tags, including the
original type signature and all implementation clauses.

Rules:
- The first line inside <AGDA_DECL> must start with exactly: {target_name} :
- Keep the type signature exactly as it is. Do not change the theorem.
- Change only the implementation clauses. You may split into pattern matches.
- Use `suc n`, never `S n`.
- Do not return helper lemmas, do not add imports, do not touch other declarations.

Current Agda file:

{source}

Agda reported this goal:

{goal_type}
{format_previous_errors(previous_errors)}
Explain briefly, then give the replacement declaration.
"""

        full_response = self.backend.generate(prompt, timeout=self.timeout).strip()

        return LLMDeclResult(
            declaration=extract_agda_declaration(full_response),
            full_response=full_response,
        )

    def ask_for_helpers_and_declaration(
        self,
        source: str,
        target_name: str,
        goal_type: str,
        previous_errors: list[str],
    ) -> LLMHelperDeclResult:
        prompt = f"""\
You are an Agda decomposition agent.

Propose helper lemma signatures, then prove {target_name} using them.

<AGDA_HELPERS> holds signatures only: no proofs, no `postulate` keyword, no
names that already exist. Helpers land in Tests.Helpers, which imports
Tests.Context, so they may not mention names local to the target file.

<AGDA_DECL> holds the full replacement declaration. Its first line must start
with exactly: {target_name} :
Keep the type signature. Change only the clauses. Use `suc n`, never `S n`.

Output format:

<AGDA_HELPERS>
helperLemma1 : ...
</AGDA_HELPERS>

<AGDA_DECL>
{target_name} : original_type_here
{target_name} ... = ...
</AGDA_DECL>

Current Agda file:

{source}

Hard goal type:

{goal_type}
{format_previous_errors(previous_errors)}
Explain briefly, then give both blocks.
"""

        full_response = self.backend.generate(prompt, timeout=self.timeout).strip()

        return LLMHelperDeclResult(
            helpers=extract_agda_helpers(full_response),
            declaration=extract_agda_declaration(full_response),
            full_response=full_response,
        )


# Backwards-compatible alias: proof_direct/proof_decompose construct
# OllamaClient(model=...).
class OllamaClient(ProofLLM):
    pass


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

_STEP_RE = re.compile(
    r"<STEP\b(?P<attrs>[^>]*)>(?P<body>.*?)</STEP>",
    re.DOTALL | re.IGNORECASE,
)
_ATTR_RE = re.compile(r"(\w+)\s*=\s*\"([^\"]*)\"")


def parse_informal_steps(text: str) -> list[InformalStep]:
    body = extract_between_tags(text, "INFORMAL_PROOF")

    if body is None:
        body = text

    steps: list[InformalStep] = []

    for position, match in enumerate(_STEP_RE.finditer(body), start=1):
        attrs = dict(_ATTR_RE.findall(match.group("attrs")))
        step_text = " ".join(match.group("body").split())

        if not step_text:
            continue

        kind = attrs.get("kind", "step").strip().lower()

        try:
            index = int(attrs.get("index", position))
        except ValueError:
            index = position

        steps.append(
            InformalStep(
                index=index,
                text=step_text,
                kind=kind if kind in {"step", "case", "induction", "lemma"} else "step",
                hard=kind == "lemma" or attrs.get("hard", "").lower() == "true",
                lemma_name=attrs.get("name") or None,
            )
        )

    if not steps:
        # Fall back to numbered/bulleted prose so a badly formatted draft is
        # still usable rather than throwing the whole sample away.
        steps = _parse_loose_steps(body)

    if not steps:
        raise ValueError("Could not parse any informal proof steps from the response.")

    return steps


def _parse_loose_steps(text: str) -> list[InformalStep]:
    steps: list[InformalStep] = []
    pattern = re.compile(r"^\s*(?:\d+[.)]|[-*])\s+(.*)$")

    for line in text.splitlines():
        match = pattern.match(line)

        if not match:
            continue

        step_text = match.group(1).strip()

        if step_text:
            steps.append(InformalStep(index=len(steps) + 1, text=step_text))

    return steps


def parse_lemma_signatures(
    block: str,
    informal: InformalProof | None = None,
) -> list[ProofObligation]:
    """
    Parse `name : signature` lines, attaching the informal step that motivated
    each lemma when the names line up.
    """

    hints: dict[str, str] = {}

    if informal is not None:
        for step in informal.steps:
            if step.lemma_name:
                hints[step.lemma_name] = step.text

    lemmas: list[ProofObligation] = []
    seen: set[str] = set()

    for line in block.strip().splitlines():
        line = line.strip()

        if not line or line.startswith("--") or line == "postulate":
            continue

        if "=" in line.split(":", 1)[0]:
            continue

        if " : " not in line:
            continue

        name, signature = line.split(" : ", 1)
        name = name.strip()
        signature = signature.strip()

        if not name or not signature or name in seen:
            continue

        if not _is_valid_agda_name(name):
            continue

        seen.add(name)
        lemmas.append(
            ProofObligation(
                name=name,
                signature=signature,
                informal_hint=hints.get(name, ""),
            )
        )

    return lemmas


def _is_valid_agda_name(name: str) -> bool:
    return bool(name) and all(char not in name for char in " \t(){}@.;")


def extract_agda_declaration(text: str) -> str:
    tagged = extract_between_tags(text, "AGDA_DECL")

    if tagged is not None:
        return tagged.strip()

    cleaned = strip_markdown_code_fences(text).strip()

    if not cleaned:
        raise ValueError("Could not extract Agda declaration from empty response.")

    return cleaned


def extract_agda_helpers(text: str) -> str:
    tagged = extract_between_tags(text, "AGDA_HELPERS")

    if tagged is None:
        raise ValueError("Could not find <AGDA_HELPERS>...</AGDA_HELPERS> block.")

    return tagged.strip()


def extract_between_tags(text: str, tag: str) -> str | None:
    start_tag = f"<{tag}>"
    end_tag = f"</{tag}>"

    start = text.find(start_tag)

    if start == -1:
        return None

    start += len(start_tag)
    end = text.find(end_tag, start)

    if end == -1:
        # Tolerate a truncated / stop-sequence-terminated response.
        return text[start:]

    return text[start:end]


def strip_markdown_code_fences(text: str) -> str:
    lines = text.strip().splitlines()

    if not lines:
        return ""

    if lines[0].strip().startswith("```"):
        lines = lines[1:]

    if lines and lines[-1].strip().startswith("```"):
        lines = lines[:-1]

    return "\n".join(lines)


def format_previous_errors(previous_errors: list[str]) -> str:
    if not previous_errors:
        return ""

    parts = ["\nPrevious failed attempts and Agda errors:\n"]

    for i, err in enumerate(previous_errors, start=1):
        parts.append(f"\nAttempt {i} failed:\n{err}\n")

    return "".join(parts)
