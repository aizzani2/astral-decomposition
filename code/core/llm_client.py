"""
LLM client for the Draft / Sketch / Prove pipeline.

Three model-facing operations, in the order the paper uses them:

    draft_informal_proof   informal statement            -> InformalProof
    sketch                 InformalProof + Agda context  -> FormalSketch text
    fill_gap               one goal type + context       -> one Agda term

Everything is transport-agnostic: `LLMBackend` is a one-method protocol, so
swapping Ollama for Claude or a hosted autoformalizer is a constructor
argument, not a rewrite. Every call goes through `ProofLLM._generate`, which
is the single place model I/O is logged.
"""

from __future__ import annotations

import re
import time
from dataclasses import dataclass, field
from typing import Any, Protocol

import requests

from core import config, prompts
from core.proof_state import (
    ContextEntry,
    InformalProof,
    InformalStep,
    LLMDeclResult,
    LLMHelperDeclResult,
    ProofObligation,
)
from core.run_log import run_logger


# ---------------------------------------------------------------------------
# Backends
# ---------------------------------------------------------------------------


@dataclass
class LLMResponse:
    """What a backend hands back. `text` is the answer; the rest is for the log."""

    text: str
    thinking: str = ""
    model: str = ""
    prompt_tokens: int | None = None
    output_tokens: int | None = None
    duration_s: float = 0.0
    stop_reason: str = ""
    extra: dict[str, Any] = field(default_factory=dict)


class LLMBackend(Protocol):
    name: str
    model: str

    def generate(
        self, prompt: str, timeout: int = 180, stop: list[str] | None = None
    ) -> LLMResponse:
        ...


@dataclass
class OllamaBackend:
    model: str = config.DEFAULT_MODEL
    base_url: str = config.OLLAMA_BASE_URL
    temperature: float = config.OLLAMA_TEMPERATURE
    top_p: float = config.OLLAMA_TOP_P
    think: bool | None = config.OLLAMA_THINK
    num_ctx: int = config.OLLAMA_NUM_CTX
    num_predict: int | None = None
    name: str = "ollama"

    def generate(
        self, prompt: str, timeout: int = 180, stop: list[str] | None = None
    ) -> LLMResponse:
        num_predict = self.num_predict

        if num_predict is None:
            num_predict = (
                config.OLLAMA_NUM_PREDICT_THINKING if self.think
                else config.OLLAMA_NUM_PREDICT
            )

        options: dict[str, object] = {
            "temperature": self.temperature,
            "top_p": self.top_p,
            "num_ctx": self.num_ctx,
            "num_predict": num_predict,
        }

        # Ollama applies stop sequences to the thinking stream too, and a
        # thinking model routinely writes the closing tag while planning, which
        # truncates the whole response to nothing. Parsing tolerates a missing
        # closing tag, so in thinking mode rely on num_predict instead.
        if stop and not self.think:
            options["stop"] = stop

        body: dict[str, object] = {
            "model": self.model,
            "prompt": prompt,
            "stream": False,
            "options": options,
        }

        if self.think is not None:
            body["think"] = self.think

        started = time.monotonic()
        response = requests.post(
            f"{self.base_url.rstrip('/')}/api/generate",
            json=body,
            timeout=timeout,
        )
        duration = time.monotonic() - started

        if response.status_code != 200:
            raise RuntimeError(
                f"Ollama returned {response.status_code}:\n{response.text}"
            )

        data = response.json()

        return LLMResponse(
            text=data.get("response", ""),
            thinking=data.get("thinking", "") or "",
            model=data.get("model", self.model),
            prompt_tokens=data.get("prompt_eval_count"),
            output_tokens=data.get("eval_count"),
            duration_s=duration,
            stop_reason=data.get("done_reason", ""),
            extra={
                "think": self.think,
                "options": options,
                "total_duration_ns": data.get("total_duration"),
                "load_duration_ns": data.get("load_duration"),
            },
        )


@dataclass
class AnthropicBackend:
    """
    Claude via the official `anthropic` SDK (optional dependency:
    `pip install anthropic`). Credentials come from the environment
    (ANTHROPIC_API_KEY or an `ant auth login` profile).

    Current Claude models take adaptive thinking and an `effort` level rather
    than a token budget or sampling temperature, so those are the only knobs.
    """

    model: str = config.ANTHROPIC_DEFAULT_MODEL
    effort: str = config.ANTHROPIC_EFFORT
    max_tokens: int = config.ANTHROPIC_MAX_TOKENS
    name: str = "anthropic"

    def __post_init__(self) -> None:
        try:
            import anthropic
        except ImportError as error:
            raise RuntimeError(
                "The Anthropic backend needs the `anthropic` package: "
                "pip install anthropic"
            ) from error

        self._client = anthropic.Anthropic()

    def generate(
        self, prompt: str, timeout: int = 180, stop: list[str] | None = None
    ) -> LLMResponse:
        kwargs: dict[str, Any] = {
            "model": self.model,
            "max_tokens": self.max_tokens,
            "thinking": {"type": "adaptive"},
            "output_config": {"effort": self.effort},
            "messages": [{"role": "user", "content": prompt}],
        }

        if stop:
            kwargs["stop_sequences"] = stop

        started = time.monotonic()
        response = self._client.with_options(timeout=float(timeout)).messages.create(**kwargs)
        duration = time.monotonic() - started

        if response.stop_reason == "refusal":
            details = getattr(response, "stop_details", None)
            raise RuntimeError(f"Claude refused the request: {details}")

        text = "".join(
            block.text for block in response.content if block.type == "text"
        )
        thinking = "".join(
            getattr(block, "thinking", "") or ""
            for block in response.content
            if block.type == "thinking"
        )

        return LLMResponse(
            text=text,
            thinking=thinking,
            model=response.model,
            prompt_tokens=response.usage.input_tokens,
            output_tokens=response.usage.output_tokens,
            duration_s=duration,
            stop_reason=response.stop_reason or "",
            extra={"effort": self.effort, "response_id": response.id},
        )


@dataclass
class EchoBackend:
    """Deterministic stub backend, for testing the harness without a model."""

    responses: list[str]
    calls: list[str] | None = None
    model: str = "echo"
    name: str = "echo"

    def generate(
        self, prompt: str, timeout: int = 180, stop: list[str] | None = None
    ) -> LLMResponse:
        if self.calls is None:
            self.calls = []

        self.calls.append(prompt)

        if not self.responses:
            raise RuntimeError("EchoBackend ran out of scripted responses.")

        return LLMResponse(text=self.responses.pop(0), model=self.model)


def make_backend(
    model: str = config.DEFAULT_MODEL,
    backend: str = config.DEFAULT_BACKEND,
    base_url: str = config.OLLAMA_BASE_URL,
    think: bool | None = config.OLLAMA_THINK,
    effort: str = config.ANTHROPIC_EFFORT,
) -> LLMBackend:
    """Pick a backend by name, or by the model id when backend == "auto"."""

    if backend == "auto":
        backend = "anthropic" if model.startswith("claude") else "ollama"

    if backend == "ollama":
        return OllamaBackend(model=model, base_url=base_url, think=think)

    if backend == "anthropic":
        return AnthropicBackend(model=model, effort=effort)

    raise ValueError(f"Unknown backend: {backend!r} (expected ollama, anthropic, auto)")


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
        model: str = config.DEFAULT_MODEL,
        base_url: str = config.OLLAMA_BASE_URL,
        timeout: int = config.LLM_TIMEOUT_SECONDS,
    ) -> None:
        self.backend = backend or make_backend(model=model, base_url=base_url)
        self.timeout = timeout
        self.calls = 0

    @property
    def model(self) -> str:
        return getattr(self.backend, "model", "?")

    def _generate(
        self, stage: str, prompt: str, stop: list[str] | None = None, **tags: Any
    ) -> str:
        """The one place model calls happen, so the one place they are logged."""

        self.calls += 1
        started = time.monotonic()

        try:
            response = self.backend.generate(prompt, timeout=self.timeout, stop=stop)
        except Exception as error:
            run_logger().event(
                "llm_call",
                stage=stage,
                model=self.model,
                backend=getattr(self.backend, "name", "?"),
                prompt=prompt,
                stop=stop,
                error=f"{type(error).__name__}: {error}",
                duration_s=round(time.monotonic() - started, 3),
                **tags,
            )
            raise

        run_logger().event(
            "llm_call",
            stage=stage,
            model=response.model or self.model,
            backend=getattr(self.backend, "name", "?"),
            prompt=prompt,
            stop=stop,
            text=response.text,
            thinking=response.thinking,
            prompt_tokens=response.prompt_tokens,
            output_tokens=response.output_tokens,
            duration_s=round(response.duration_s, 3),
            stop_reason=response.stop_reason,
            extra=response.extra,
            **tags,
        )

        return response.text

    # -- stage 1: draft ----------------------------------------------------

    def draft_informal_proof(
        self,
        informal_statement: str,
        formal_signature: str,
        extra_context: str = "",
        sample_index: int = 0,
    ) -> InformalProof:
        prompt = prompts.DRAFT_TEMPLATE.format(
            system=prompts.DRAFT_SYSTEM,
            few_shot=prompts.DRAFT_FEW_SHOT,
            informal_statement=informal_statement.strip(),
            formal_signature=formal_signature.strip(),
            extra_context=(extra_context + "\n") if extra_context else "",
        )

        raw = self._generate(
            "draft", prompt, stop=["</INFORMAL_PROOF>"], sample_index=sample_index
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

        for index in range(n_samples):
            try:
                draft = self.draft_informal_proof(
                    informal_statement=informal_statement,
                    formal_signature=formal_signature,
                    extra_context=extra_context,
                    sample_index=index,
                )
            except (ValueError, RuntimeError) as error:
                run_logger().event(
                    "draft", sample_index=index, ok=False, error=str(error)
                )
                continue

            run_logger().event(
                "draft",
                sample_index=index,
                ok=True,
                steps=draft.steps,
                n_lemma_steps=sum(1 for s in draft.steps if s.hard),
                raw=draft.raw,
            )
            drafts.append(draft)

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
        attempt: int = 0,
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

        raw = self._generate("sketch", prompt, stop=["</AGDA_SKETCH>"], attempt=attempt)

        # The prompt ends with an open <AGDA_LEMMAS> tag, so the model's
        # continuation is the body. Re-attach it before parsing.
        text = "<AGDA_LEMMAS>" + raw if "<AGDA_LEMMAS>" not in raw else raw

        lemma_block = extract_between_tags(text, "AGDA_LEMMAS") or ""
        sketch = extract_between_tags(text, "AGDA_SKETCH")

        if sketch is None:
            sketch = strip_markdown_code_fences(text).strip()
        else:
            sketch = strip_markdown_code_fences(sketch).strip()

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
        target_name: str = "",
        attempt: int = 0,
    ) -> str:
        prompt = prompts.GAP_TEMPLATE.format(
            goal_type=goal_type.strip(),
            context="\n".join(f"  {e.name} : {e.type}" for e in context) or "  (empty)",
            informal_hint=informal_hint.strip() or "(none recorded)",
            available_names=available_names or "(none listed)",
            excerpt=excerpt,
            error_text=format_previous_errors(previous_errors or []),
            target_name=target_name or "the current function",
        )

        raw = self._generate("gap", prompt, stop=["</AGDA_TERM>"], attempt=attempt)
        text = "<AGDA_TERM>" + raw if "<AGDA_TERM>" not in raw else raw

        term = extract_between_tags(text, "AGDA_TERM")

        if term is None:
            term = strip_markdown_code_fences(raw)

        term = strip_markdown_code_fences(term).strip()

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
        informal_hint: str = "",
        available_names: str = "",
        target_name: str = "",
    ) -> str:
        prompt = prompts.LEMMA_FROM_GAP_TEMPLATE.format(
            lemma_name=lemma_name,
            goal_type=goal_type.strip(),
            context="\n".join(f"  {e.name} : {e.type}" for e in context) or "  (empty)",
            context_module=context_module,
            informal_hint=informal_hint.strip() or "(none recorded)",
            available_names=available_names or "(none listed)",
            target_name=target_name or "the current function",
        )

        raw = self._generate("lemma_signature", prompt, stop=["</AGDA_SIG>"])
        text = raw

        if "<AGDA_SIG>" in raw:
            text = extract_between_tags(raw, "AGDA_SIG") or raw

        text = strip_markdown_code_fences(text)

        # First line that looks like a type: models wrap in fences, echo the
        # tag, or add a sentence first.
        candidates = [line.strip() for line in text.splitlines() if line.strip()]
        typed = [c for c in candidates if "→" in c or "->" in c or "≡" in c]
        first_line = (typed or candidates or [""])[0]

        if first_line.startswith(f"{lemma_name} :"):
            first_line = first_line.split(":", 1)[1]
        elif first_line.startswith(":"):
            first_line = first_line[1:]

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

        full_response = self._generate("direct", prompt).strip()

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

        full_response = self._generate("decompose", prompt).strip()

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
    # The prompt ends with an open <INFORMAL_PROOF>, so the model continues
    # with the body and frequently emits a stray "<INFORMAL_PROOF>" *after*
    # the steps in place of the closing tag. Steps are unambiguous, so scan
    # the whole text for them; only the loose-prose fallback needs the body.
    body = extract_between_tags(text, "INFORMAL_PROOF")

    if body is None or not _STEP_RE.search(body):
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

    for line in strip_markdown_code_fences(block).strip().splitlines():
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
    """Drop ``` fences anywhere in the text (models add them despite the tags)."""

    lines = text.strip().splitlines()

    if not lines:
        return ""

    return "\n".join(line for line in lines if not line.strip().startswith("```"))


def format_previous_errors(previous_errors: list[str]) -> str:
    if not previous_errors:
        return ""

    parts = ["\nPrevious failed attempts and Agda errors:\n"]

    for i, err in enumerate(previous_errors, start=1):
        parts.append(f"\nAttempt {i} failed:\n{err}\n")

    return "".join(parts)
