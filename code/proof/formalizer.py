"""
The autoformalize fine-tune as DSP's formal writer.

DSP needs two skills: planning a proof in prose (the draft) and writing Agda
(the sketch). astral-expmath/qwen3.5-4b-agda-autoformalize-context is trained
for the second only: given an Agda file's header and the lines above an
insertion point, a declaration name and an informal statement, it writes the
declaration. It takes no chat prompt, so it cannot draft; it cannot leave holes
on purpose either.

`FormalizerLLM` is a `ProofLLM` whose stages are split accordingly:

    draft     delegated to a chat model (`drafter`)
    sketch    for each lemma the draft names, the formalizer writes it from the
              step's text and its signature becomes the lemma's statement;
              then it writes the target's proof with the target's signature
              fixed, the lemmas postulated above it and the draft as comments
              in its context. Holes come from where that proof fails
              (proof/holes.py, enabled by prove_dsp's `place_holes`)
    a stuck   becomes a lemma stating exactly the hole (no model call): its
    hole      goal, written as Agda prints it unnormalised, over the variables
              its clause binds and the hypotheses about them; the lemma is
              then proved by the same pipeline, one level down

So its `sketch` breaks the sketch-prompt rules the chat sketch follows (it
writes `with`, `rewrite` and chains, and no holes), which is why
`sketch_rules` is off.
"""

from __future__ import annotations

import re
from typing import Any

from core.llm_client import LLMBackend, ProofLLM
from core.proof_state import ContextEntry, InformalProof, ProofObligation
from proof.holes import split_declaration
from util.agda_source import QUALIFIED_RE, WORD_RE, declaration_span
from util.sketch_ops import mask_comments

STOP = ["<|im_end|>", "</formal>"]

# Lines that belong to a file's header (everything before its first declaration).
HEADER_LINE = re.compile(r"^\s*(?:$|--|\{-|-\}|module\s|open\s|import\s|```)")


class FormalizerLLM(ProofLLM):
    sketch_rules = False      # real Agda: `with`, `rewrite`, chains are all fine
    states_gap_goals = True   # a stuck hole becomes a lemma stating exactly its goal

    def __init__(
        self,
        drafter: ProofLLM,
        backend: LLMBackend,
        path: str = "",
        max_lemmas: int = 3,
        timeout: int = 600,
    ) -> None:
        super().__init__(backend=backend, timeout=timeout)
        self.drafter = drafter
        self.path = path            # the file's path relative to its library, for the prompt
        self.max_lemmas = max_lemmas

    # -- draft: the chat model's ------------------------------------------

    def draft_informal_proof(self, *args: Any, **kwargs: Any) -> InformalProof:
        return self.drafter.draft_informal_proof(*args, **kwargs)

    def draft_informal_proofs(self, *args: Any, **kwargs: Any) -> list[InformalProof]:
        return self.drafter.draft_informal_proofs(*args, **kwargs)

    # -- sketch -------------------------------------------------------------

    def sketch(
        self,
        source: str,
        target_name: str,
        signature: str,
        informal: InformalProof,
        available_names: str = "",
        previous_errors: list[str] | None = None,
        helpers_module: str = "",
        context_module: str = "",
        attempt: int = 0,
    ) -> tuple[list[ProofObligation], str, str]:
        """(lemmas stated from the draft, the target's declaration, raw completions)."""

        parts = prompt_parts(source, target_name, self.path)
        taken = set(WORD_RE.findall(source))
        lemmas: list[ProofObligation] = []
        raw: list[str] = []

        for step in [s for s in informal.steps if s.hard][: self.max_lemmas]:
            name = _fresh(step.lemma_name or "", f"{target_name}-lemma", taken)
            completion = self._declaration(parts, name, step.text, lemmas)
            raw.append(completion)
            statement, _proof = split_declaration(completion, name)

            if statement:
                lemmas.append(ProofObligation(name=name, signature=statement, informal_hint=step.text))

        completion = self._declaration(
            parts, target_name, informal.statement, lemmas,
            signature=parts["signature"], sketch=informal.as_numbered_text(),
        )
        raw.append(completion)

        return lemmas, parts["signature"].rstrip("\n") + "\n" + completion, "\n\n".join(raw)

    def _declaration(
        self,
        parts: dict[str, str],
        name: str,
        informal: str,
        lemmas: list[ProofObligation],
        signature: str = "",
        sketch: str = "",
    ) -> str:
        """The formalizer's text for `name`, written at the target's place."""

        pad = parts["pad"]
        context = parts["context"]

        if lemmas:
            context += "".join(
                f"{pad}postulate\n{pad}  {l.name} : {l.signature}\n\n" for l in lemmas
            )
        if sketch:
            context += "".join(f"{pad}-- {line}\n" for line in ("Proof sketch:", *sketch.splitlines()))

        context = "".join(context.splitlines(keepends=True)[-80:]) + pad
        prompt = (
            f"<file>{parts['file']}</file>\n<header>\n{parts['header']}</header>\n"
            f"<context>\n{context}</context>\n<name>{name}</name>\n"
            f"<informal>{informal.strip()}</informal>\n<formal>"
        )

        if signature:
            prompt += signature.rstrip("\n") + "\n"

        return self.complete("formalize", prompt, stop=STOP, declaration=name)

    # -- prove ----------------------------------------------------------------

    def fill_gap(self, *args: Any, **kwargs: Any) -> str:
        raise ValueError("The formalizer writes declarations, not single terms.")

    def lemma_signature_for_gap(
        self,
        lemma_name: str,
        goal_type: str,
        context: list[ContextEntry],
        bound: set[str] | None = None,
        **_: Any,
    ) -> str:
        """The hole's goal over the context variables it uses; no model call."""

        goal = " ".join(goal_type.split())

        if QUALIFIED_RE.search(goal):
            raise ValueError("The goal names things the file has not brought into scope.")

        binders = sequent_binders(context, bound)

        if QUALIFIED_RE.search(binders):
            raise ValueError("A variable's type names things not in scope.")

        return binders + goal


def sequent_binders(context: list[ContextEntry], bound: set[str] | None = None) -> str:
    """
    Binders for a lemma stating a hole exactly: its context, in binding order
    (hypotheses included: a goal alone usually is not provable). A variable
    not in scope by name becomes implicit, for Agda to infer at the call.

    With `bound` (the names the hole's clause binds), only those, the hidden
    variables, and whatever their types mention are quantified: the rest of
    the context is the module's parameters, which the lemma, placed in the
    same module, already has. Restating them only drags in their types,
    which often print with qualified names.
    """

    hidden = {e.name for e in context if not e.in_scope}
    types = {e.name: " ".join(e.type.split()) for e in context}

    if bound is None:
        keep = set(types)
    else:
        keep = {n for n in types if n in bound or n in hidden}
        while True:
            more = {n for n in types if n not in keep and any(n in WORD_RE.findall(types[k]) for k in keep)}
            if not more:
                break
            keep |= more

    return "".join(
        f"{{{n} : {types[n]}}} → " if n in hidden else f"({n} : {types[n]}) → "
        for n in types if n in keep
    )


def prompt_parts(source: str, target: str, path: str = "") -> dict[str, str]:
    """
    The pieces of the formalizer's prompt for writing `target` where it
    stands in `source`: the header (the file up to its first declaration),
    the context (up to 80 lines between the header and the target), the
    target's signature (dedented) and its indentation.
    """

    sig_start, body_start, _, column = declaration_span(source, target)
    masked = mask_comments(source)
    offset = 0
    header_end = 0

    for line in masked.splitlines(keepends=True):
        if offset >= sig_start:
            break
        if not HEADER_LINE.match(line):
            header_end = offset + len(line) - len(line.lstrip(" "))
            break
        offset += len(line)
        header_end = offset

    header_end = min(header_end, sig_start)
    signature = "".join(
        line[min(column, len(line) - len(line.lstrip())):]
        for line in source[sig_start:body_start].splitlines(keepends=True)
    )

    return {
        "file": path or "Main.agda",
        "header": source[:header_end],
        "context": "".join(source[header_end:sig_start].splitlines(keepends=True)[-80:]),
        "signature": signature,
        "pad": " " * column,
    }


def _fresh(suggested: str, fallback: str, taken: set[str]) -> str:
    base = suggested if re.fullmatch(r"[^\s(){};.@\"]+", suggested or "") else fallback
    candidate, k = base, 1

    while candidate in taken:
        k += 1
        candidate = f"{base}{k}"

    taken.add(candidate)

    return candidate
