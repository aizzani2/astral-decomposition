"""
Draft, Sketch, Prove for Agda.

    informal statement
        -> informal proof with delineated steps          (draft)
        -> Agda skeleton with holes + postulated lemmas  (sketch)
        -> each hole closed by hammer / model            (prove)
        -> each lemma discharged by recursing on this whole pipeline

The pipeline is deliberately staged so that a failure tells you *where* it
failed: a bad skeleton is a different problem from a skeleton whose gaps are
too wide, and only the second one is worth throwing more compute at.

Helpers-file discipline (this bit is easy to get wrong):

    * Tests.Helpers accumulates *proved* lemma declarations, appended one at
      a time as they are discharged.
    * While a sketch is being checked and its gaps closed, the lemmas it
      declares are appended as a `postulate` block. That block is removed
      (by restoring the snapshot taken at entry) before the lemmas are proved,
      so nothing is ever proved from an unproved assumption.
    * Nothing here ever *overwrites* the helpers file. A nested lemma's
      sketch used to reset it, wiping the sibling lemmas its parent had
      already proved; the parent's final check then failed with
      "not in scope".
"""

from __future__ import annotations

from pathlib import Path
import re

from core.agda_client import check_sketch, run_plain_agda
from core.config import (
    AGDA_IMPORT_PATH,
    DEFAULT_MODEL,
    GAP_LLM_ATTEMPTS,
    DRAFT_SAMPLES,
    MAX_DEPTH,
    SKETCH_MAX_ATTEMPTS,
)
from core.hammer import HammerConfig, close_gap
from core.llm_client import ProofLLM, parse_informal_steps
from core.proof_context import get_signature_line, infer_target_name_from_first_hole
from core.proof_files import (
    preserved_file,
    append_helper_declaration,
    append_postulates,
    restore_file,
    save_file,
    write_helper_goal_file,
)
from core.proof_history import ProofHistory
from core.proof_state import (
    DSPResult,
    FormalSketch,
    GapResult,
    InformalProof,
    ProofObligation,
    SketchGap,
)
from core.run_log import run_logger
from util.sketch_ops import (
    available_signatures,
    build_gaps,
    count_holes,
    hint_names,
    replace_hole,
    context_signatures,
)
from util.source_edit import ensure_import, replace_top_level_decl


HELPERS_IMPORT = "open import Tests.Helpers"
HELPERS_MODULE = "Tests.Helpers"
CONTEXT_MODULE = "Tests.Context"

# Files whose declarations are *not* in scope from the target: never offer
# them as names or Mimer hints.
NON_CONTEXT_FILES = frozenset({"Target", "HelperGoal", "Helpers"})


def prove_dsp(agda_file: Path, helpers_file: Path, *args, **kwargs) -> DSPResult:
    original_helpers = save_file(helpers_file)

    with preserved_file(agda_file):
        try:
            return _prove_dsp(agda_file, helpers_file, *args, **kwargs)
        except BaseException:
            restore_file(helpers_file, original_helpers)
            raise


def _prove_dsp(
    agda_file: Path,
    helpers_file: Path,
    helper_goal_file: Path,
    informal_statement: str | None = None,
    informal_proof_text: str | None = None,
    llm: ProofLLM | None = None,
    model: str = DEFAULT_MODEL,
    depth: int = 0,
    draft_samples: int = DRAFT_SAMPLES,
    **kwargs,
) -> DSPResult:
    llm = llm or ProofLLM(model=model)
    log = run_logger()
    hammer: HammerConfig | None = kwargs.get("hammer")
    import_path = hammer.import_path if hammer is not None else AGDA_IMPORT_PATH

    source = save_file(agda_file)

    if source is None:
        return DSPResult(
            success=False, target_name="<unknown>",
            output=f"File does not exist: {agda_file}",
        )

    try:
        target_name, _goal, _load = infer_target_name_from_first_hole(
            agda_file, import_path=import_path
        )
    except ValueError as error:
        return DSPResult(success=False, target_name="<unknown>", output=str(error))

    signature_line = get_signature_line(source, target_name)
    statement = informal_statement or (
        f"Prove the following statement, given in Agda notation:\n{signature_line}"
    )

    with log.scope(target=target_name, depth=depth):
        # A human-written proof skips drafting entirely.
        if informal_proof_text:
            try:
                drafts = [
                    InformalProof(
                        statement=statement,
                        steps=parse_informal_steps(informal_proof_text),
                        raw=informal_proof_text,
                    )
                ]
            except ValueError:
                return DSPResult(
                    success=False, target_name=target_name,
                    output="Could not parse the supplied informal proof.",
                )
        else:
            # Only spend the sampling budget at the top level; recursive calls
            # would multiply it by the number of lemmas.
            samples = draft_samples if depth == 0 else 1

            drafts = llm.draft_informal_proofs(
                informal_statement=statement,
                formal_signature=signature_line,
                n_samples=samples,
            )

            # Prefer drafts that break work out into lemmas: those are the ones
            # whose sketches declare the auxiliary facts the gaps will need.
            drafts.sort(key=lambda d: -sum(1 for step in d.steps if step.hard))

        log.event(
            "drafts_ready",
            n_requested=draft_samples if depth == 0 else 1,
            n_usable=len(drafts),
            statement=statement,
        )

        if not drafts:
            result = DSPResult(
                success=False, target_name=target_name,
                output="Could not obtain a usable informal proof draft.",
            )
            log.event("dsp_result", success=False, stage="draft", output=result.output)
            return result

        last: DSPResult | None = None

        for draft_index, draft in enumerate(drafts):
            with log.scope(draft_index=draft_index):
                result = _attempt_dsp(
                    agda_file=agda_file,
                    helpers_file=helpers_file,
                    helper_goal_file=helper_goal_file,
                    informal=draft,
                    target_name=target_name,
                    signature_line=signature_line,
                    llm=llm,
                    model=model,
                    depth=depth,
                    **kwargs,
                )

            if result.success:
                return result

            last = result
            restore_file(agda_file, source)

        return last


def _attempt_dsp(
    agda_file: Path,
    helpers_file: Path,
    helper_goal_file: Path,
    informal: InformalProof,
    target_name: str,
    signature_line: str,
    llm: ProofLLM | None = None,
    model: str = DEFAULT_MODEL,
    sketch_max_attempts: int = SKETCH_MAX_ATTEMPTS,
    hammer: HammerConfig | None = None,
    max_depth: int = MAX_DEPTH,
    depth: int = 0,
    history: ProofHistory | None = None,
    verbose: bool = True,
) -> DSPResult:
    llm = llm or ProofLLM(model=model)
    history = history or ProofHistory()
    hammer = hammer or HammerConfig(llm_attempts=GAP_LLM_ATTEMPTS)
    log = run_logger()

    indent = "  " * depth

    def fail(stage: str, **fields) -> DSPResult:
        result = DSPResult(success=False, target_name=target_name, informal=informal, **fields)
        log.event("dsp_result", success=False, stage=stage, output=result.output)
        return result

    if depth > max_depth:
        return fail("depth", output=f"Maximum recursion depth exceeded: {max_depth}")

    original_source = save_file(agda_file)
    original_helpers = save_file(helpers_file)

    if original_source is None:
        return fail("io", output=f"File does not exist: {agda_file}")

    if verbose:
        print(f"\n{indent}=== DSP on {target_name} (depth {depth}) ===")
        print(f"{indent}Informal proof:")
        for step in informal.steps:
            print(f"{indent}  {step.index}. [{step.kind}] {step.text[:100]}")

    # --------------------------------------------------------------- sketch
    sketch, sketch_errors = _build_sketch(
        agda_file=agda_file,
        helpers_file=helpers_file,
        original_source=original_source,
        target_name=target_name,
        signature_line=signature_line,
        informal=informal,
        llm=llm,
        max_attempts=sketch_max_attempts,
        history=history,
        import_path=hammer.import_path,
        verbose=verbose,
        indent=indent,
    )

    if sketch is None:
        restore_file(agda_file, original_source)
        restore_file(helpers_file, original_helpers)

        return fail(
            "sketch",
            output="Sketch stage failed:\n" + "\n\n".join(sketch_errors[-2:]),
        )

    if verbose:
        print(
            f"{indent}Sketch accepted: {len(sketch.gaps)} gap(s), "
            f"{len(sketch.lemmas)} lemma(s)."
        )

    # ---------------------------------------------------------------- prove
    context_sigs = context_signatures(Path(hammer.import_path), exclude=NON_CONTEXT_FILES)
    helpers_now = helpers_file.read_text() if helpers_file.exists() else ""

    names = available_signatures(sketch.source, helpers_now, context_sigs)

    # Mimer hints: imported lemmas only. Mimer already tries recursive calls
    # by itself, and naming the function under definition as a hint makes
    # the search blow up (5s -> no solution on a gap it otherwise closes in
    # under a second). Names local to the target file are therefore excluded.
    hints = hint_names(helpers_now, context_sigs)

    log.event("prove_start", n_gaps=len(sketch.gaps), mimer_hints=hints)

    working_source = sketch.source
    gap_results: list[GapResult] = []
    promoted: list[ProofObligation] = []
    failed: list[GapResult] = []

    for gap in sorted(sketch.gaps, key=lambda g: g.hole_index, reverse=True):
        if verbose:
            print(f"{indent}  gap {gap.hole_index}: {gap.goal_type[:80]}")

        result = close_gap(
            agda_file=agda_file,
            source=working_source,
            gap=gap,
            llm=llm,
            config=hammer,
            available_names=names,
            mimer_hints=hints,
            target_name=target_name,
            verbose=verbose,
        )

        if not result.success:
            result = _promote_gap_to_lemma(
                agda_file=agda_file,
                helpers_file=helpers_file,
                source=working_source,
                gap=gap,
                llm=llm,
                hammer=hammer,
                existing_lemmas=sketch.lemmas + promoted,
                target_name=target_name,
                available_names=names,
                mimer_hints=hints,
                verbose=verbose,
                indent=indent,
            )

            if result.success and result.method.startswith("lemma:"):
                promoted.append(_lemma_from_method(result))

        gap_results.append(result)

        if not result.success:
            failed.append(result)
            continue

        working_source = replace_hole(
            working_source, gap.hole_index, result.solution or ""
        )

    if failed:
        restore_file(agda_file, original_source)
        restore_file(helpers_file, original_helpers)

        return fail(
            "gaps",
            sketch=sketch,
            gap_results=gap_results,
            output="\n\n".join(
                f"Gap {r.gap.hole_index} ({r.gap.goal_type}):\n{r.output}"
                for r in failed
            ),
        )

    agda_file.write_text(working_source)

    if count_holes(working_source) != 0:
        restore_file(agda_file, original_source)
        restore_file(helpers_file, original_helpers)

        return fail(
            "gaps",
            sketch=sketch,
            gap_results=gap_results,
            output="Holes remain in the completed proof; sketch/goal mismatch.",
        )

    # ------------------------------------------------------ discharge lemmas
    obligations = sketch.lemmas + promoted
    lemma_results: list[DSPResult] = []

    if obligations:
        # Drop this level's postulates; keep everything proved so far.
        restore_file(helpers_file, original_helpers)

        for obligation in obligations:
            if verbose:
                print(f"{indent}  discharging lemma {obligation.name}")

            log.event(
                "lemma_start", lemma=obligation.name,
                signature=obligation.signature, hint=obligation.informal_hint,
            )

            write_helper_goal_file(
                helper_goal_file=helper_goal_file,
                obligation=obligation,
            )

            lemma_result = prove_dsp(
                agda_file=helper_goal_file,
                helpers_file=helpers_file,
                helper_goal_file=helper_goal_file,
                informal_statement=obligation.informal_hint or None,
                llm=llm,
                model=model,
                sketch_max_attempts=sketch_max_attempts,
                hammer=hammer,
                max_depth=max_depth,
                depth=depth + 1,
                history=history,
                verbose=verbose,
            )

            lemma_results.append(lemma_result)

            log.event(
                "lemma_end", lemma=obligation.name,
                success=lemma_result.success, output=lemma_result.output,
            )

            if not lemma_result.success:
                restore_file(agda_file, original_source)
                restore_file(helpers_file, original_helpers)

                return fail(
                    "lemma",
                    sketch=sketch,
                    gap_results=gap_results,
                    lemma_results=lemma_results,
                    output=(
                        f"Lemma {obligation.name} could not be proved.\n"
                        f"{lemma_result.output}"
                    ),
                )

            append_helper_declaration(
                helpers_file=helpers_file,
                declaration=_declaration_of(lemma_result, obligation),
            )

    # ----------------------------------------------------------- final check
    agda_file.write_text(working_source)
    final = run_plain_agda(agda_file, import_path=hammer.import_path)

    leftover_postulates = "postulate" in helpers_file.read_text()

    if not final.success or leftover_postulates:
        restore_file(agda_file, original_source)
        restore_file(helpers_file, original_helpers)

        message = final.output

        if leftover_postulates:
            message += "\n\nHelpers file still contains postulates."

        return fail(
            "final_check",
            sketch=sketch,
            gap_results=gap_results,
            lemma_results=lemma_results,
            output=message,
        )

    result = DSPResult(
        success=True,
        target_name=target_name,
        informal=informal,
        sketch=sketch,
        gap_results=gap_results,
        lemma_results=lemma_results,
        final_source=working_source,
        output=final.output,
    )

    log.event(
        "dsp_result", success=True, stage="done",
        final_source=working_source,
        helpers_source=helpers_file.read_text(),
        gap_methods=[r.method for r in gap_results],
    )

    return result


# ---------------------------------------------------------------------------
# Stage helpers
# ---------------------------------------------------------------------------

def _build_sketch(
    agda_file: Path,
    helpers_file: Path,
    original_source: str,
    target_name: str,
    signature_line: str,
    informal: InformalProof,
    llm: ProofLLM,
    max_attempts: int,
    history: ProofHistory,
    import_path: str,
    verbose: bool,
    indent: str,
) -> tuple[FormalSketch | None, list[str]]:
    """
    Ask for a skeleton until one typechecks with holes.

    The success condition here is *not* a complete proof: it is "Agda accepts
    the structure and reports N interaction points".
    """

    log = run_logger()
    errors: list[str] = []
    previous_errors = history.messages_for_target(target_name)
    helpers_snapshot = save_file(helpers_file)

    context_sigs = context_signatures(Path(import_path), exclude=NON_CONTEXT_FILES)
    proved_helpers = available_signatures(helpers_snapshot or "")
    names = "\n".join(part for part in (context_sigs, proved_helpers) if part)

    for attempt in range(1, max_attempts + 1):
        if verbose:
            print(f"{indent}Sketch attempt {attempt}...")

        def reject(reason: str, message: str, **fields) -> None:
            errors.append(message)
            log.event(
                "sketch_attempt", attempt=attempt, accepted=False,
                reason=reason, message=message, **fields,
            )

        try:
            lemmas, sketch_text, raw = llm.sketch(
                source=original_source,
                target_name=target_name,
                signature=signature_line,
                informal=informal,
                available_names=names,
                previous_errors=previous_errors,
                helpers_module=HELPERS_MODULE,
                context_module=CONTEXT_MODULE,
                attempt=attempt,
            )
        except (ValueError, RuntimeError) as error:
            reject("parse", str(error))
            previous_errors = previous_errors + [f"Parse failure: {error}"]
            continue

        first_line = _first_code_line(sketch_text)

        if _normalise(first_line) != _normalise(signature_line):
            message = (
                "The sketch changed the target type signature.\n"
                f"Expected: {signature_line}\nGot:      {first_line}"
            )
            reject("signature", message, sketch=sketch_text, lemmas=lemmas, raw=raw)
            previous_errors = previous_errors + [message]
            continue

        # Lemmas may not shadow the target or anything already in scope.
        lemmas, dropped_lemmas = _filter_lemmas(lemmas, target_name, names)

        # Small models like to prove the lemmas inline. Those clauses can only
        # break the file (the lemma is postulated), so drop them and log it.
        sketch_text, dropped_clauses = _keep_target_clauses(sketch_text, target_name)

        if dropped_lemmas or dropped_clauses:
            log.event(
                "sketch_repair", attempt=attempt,
                dropped_lemmas=dropped_lemmas, dropped_clauses=dropped_clauses,
            )

        syntax_problem = _obvious_syntax_problem(sketch_text)

        if syntax_problem:
            reject("syntax", syntax_problem, sketch=sketch_text, lemmas=lemmas, raw=raw)
            previous_errors = previous_errors + [
                f"Rejected before typechecking: {syntax_problem}\n\nYour sketch was:\n{sketch_text}"
            ]
            continue

        if count_holes(sketch_text) == 0:
            # Not fatal: a hole-free sketch is just a direct proof attempt.
            if verbose:
                print(f"{indent}  (sketch has no holes; treating as a direct proof)")

        # Postulate this sketch's lemmas on top of whatever is already proved.
        restore_file(helpers_file, helpers_snapshot)
        append_postulates(helpers_file, lemmas)

        trial = replace_top_level_decl(
            source=ensure_import(original_source, HELPERS_IMPORT),
            name=target_name,
            replacement=sketch_text,
        )

        agda_file.write_text(trial)
        check = check_sketch(agda_file, import_path=import_path, with_context=True)

        if check.kind == "error":
            history.add(
                phase="sketch",
                target_name=target_name,
                candidate=sketch_text,
                agda_output=check.message,
            )
            reject("agda", check.message, sketch=sketch_text, lemmas=lemmas, raw=raw)
            previous_errors = history.messages_for_target(target_name)
            continue

        gaps = build_gaps(trial, check.goals)

        log.event(
            "sketch_attempt", attempt=attempt, accepted=True,
            sketch=sketch_text, lemmas=lemmas, raw=raw, trial_source=trial,
            n_holes=count_holes(trial), n_goals=len(check.goals),
            gaps=gaps,
        )

        if count_holes(trial) != len(check.goals) and verbose:
            print(
                f"{indent}  warning: {count_holes(trial)} textual holes but Agda "
                f"reports {len(check.goals)} goals"
            )

        return (
            FormalSketch(
                target_name=target_name,
                signature=signature_line,
                source=trial,
                lemmas=lemmas,
                gaps=gaps,
                raw_response=raw,
            ),
            errors,
        )

    restore_file(helpers_file, helpers_snapshot)
    return None, errors


def _filter_lemmas(
    lemmas: list[ProofObligation], target_name: str, available: str
) -> tuple[list[ProofObligation], list[str]]:
    taken = {target_name}

    for line in available.splitlines():
        head = line.split(":", 1)[0].strip()
        if head:
            taken.add(head)

    kept = [lemma for lemma in lemmas if lemma.name not in taken]
    dropped = [lemma.name for lemma in lemmas if lemma.name in taken]

    return kept, dropped


def _keep_target_clauses(sketch_text: str, target_name: str) -> tuple[str, list[str]]:
    """
    Keep only the top-level blocks that belong to the target: its signature
    and clauses (`target ...`), together with the comments directly above
    them and any indented continuation lines. Everything else is returned as
    dropped text for the log.
    """

    lines = sketch_text.splitlines()
    kept: list[str] = []
    dropped: list[str] = []
    pending_comments: list[str] = []
    keeping = True

    for line in lines:
        stripped = line.strip()

        if not stripped:
            (kept if keeping else dropped).append(line)
            continue

        if stripped.startswith("--") and not line.startswith((" ", "\t")):
            pending_comments.append(line)
            continue

        if line.startswith((" ", "\t")) or stripped.startswith(("...", "|")):
            # Continuation of whatever block we are in.
            (kept if keeping else dropped).append(line)
            continue

        head = re.split(r"[\s(){}]", stripped, maxsplit=1)[0]
        keeping = head == target_name

        (kept if keeping else dropped).extend(pending_comments)
        pending_comments = []
        (kept if keeping else dropped).append(line)

    kept.extend(pending_comments)
    dropped_blocks = [l for l in dropped if l.strip() and not l.strip().startswith("--")]

    return "\n".join(kept).strip() + "\n", dropped_blocks


_FORBIDDEN_SKETCH_SYNTAX = (
    ("?_", "`?_` is not Agda; the only hole syntax is {!!}."),
    ("...", "`...` (with-abstraction) is not allowed; pattern match on the arguments and put a hole on each right-hand side."),
    (" with ", "`with` is not allowed in the sketch; pattern match on the arguments and put a hole on each right-hand side."),
    (" rewrite ", "`rewrite` is not allowed in the sketch; leave the right-hand side as a hole {!!}."),
)


def _obvious_syntax_problem(sketch_text: str) -> str:
    code = "\n".join(
        line.split("--", 1)[0] for line in sketch_text.splitlines()
    )

    for needle, message in _FORBIDDEN_SKETCH_SYNTAX:
        if needle in code:
            return message

    return ""


def _first_code_line(text: str) -> str:
    for line in text.splitlines():
        stripped = line.strip()

        if stripped and not stripped.startswith("--"):
            return stripped

    return ""


def _normalise(line: str) -> str:
    return " ".join(line.replace("->", "→").split())


def _plausible_signature(signature: str) -> bool:
    """Cheap filter for prompt echoes and prose before Agda sees the text."""

    if not signature or "\n" in signature or len(signature) > 400:
        return False

    if re.search(r"</?[A-Z_]+>|```", signature):
        return False

    return "→" in signature or "->" in signature or "≡" in signature or "==" in signature


def _is_degenerate(signature: str, goal_type: str) -> bool:
    """A lemma that just restates the goal buys nothing and recurses forever."""
    def norm(s: str) -> str:
        s = re.sub(r"∀\s*[^→]*→", "", s)
        s = re.sub(r"\([^:]+:[^)]+\)\s*→", "", s)
        return " ".join(s.split())
    return norm(signature) == norm(goal_type)


def _promote_gap_to_lemma(
    agda_file: Path,
    helpers_file: Path,
    source: str,
    gap: SketchGap,
    llm: ProofLLM,
    hammer: HammerConfig,
    existing_lemmas: list[ProofObligation],
    target_name: str,
    available_names: str,
    mimer_hints: list[str],
    verbose: bool,
    indent: str,
) -> GapResult:
    """
    Last resort for a stuck hole: abstract it into a top-level lemma, postulate
    the lemma, and apply it to the in-scope variables. The lemma then has to be
    proved recursively, which is how the paper's "hard step becomes its own
    lemma" idea shows up here.
    """

    log = run_logger()
    lemma_name = _fresh_lemma_name(target_name, gap.hole_index, existing_lemmas)

    if verbose:
        print(f"{indent}  promoting gap {gap.hole_index} to lemma {lemma_name}")

    try:
        signature = llm.lemma_signature_for_gap(
            lemma_name=lemma_name,
            goal_type=gap.goal_type,
            context=gap.context,
            context_module=CONTEXT_MODULE,
            informal_hint=gap.informal_hint,
            available_names=available_names,
            target_name=target_name,
        )
    except (ValueError, RuntimeError) as error:
        log.event("promote", hole_index=gap.hole_index, lemma=lemma_name, ok=False, error=str(error))
        return GapResult(success=False, gap=gap, method="failed", output=str(error))

    if not _plausible_signature(signature):
        log.event(
            "promote", hole_index=gap.hole_index, lemma=lemma_name,
            signature=signature, ok=False, error="implausible signature",
        )
        return GapResult(
            success=False, gap=gap, method="failed",
            output=f"Model returned an implausible lemma signature: {signature!r}",
        )

    if _is_degenerate(signature, gap.goal_type):
        log.event(
            "promote", hole_index=gap.hole_index, lemma=lemma_name,
            signature=signature, ok=False, error="degenerate",
        )
        return GapResult(
            success=False, gap=gap, method="failed",
            output=(
                f"Refusing to promote: lemma {lemma_name} restates the goal "
                f"({signature}) and would not simplify it."
            ),
        )

    obligation = ProofObligation(
        name=lemma_name,
        signature=signature,
        informal_hint=gap.informal_hint,
    )

    # Append rather than rewrite: the parent may already have proved and
    # appended sibling lemmas that its final check depends on.
    saved_helpers = helpers_file.read_text()
    append_postulates(helpers_file, [obligation])

    variables = [entry.name for entry in gap.context if entry.in_scope]
    candidates = [lemma_name] + [
        f"{lemma_name} {' '.join(variables[:k])}"
        for k in range(len(variables), 0, -1)
    ]

    config = HammerConfig(
        tactics=tuple(candidates),
        use_mimer=True,
        llm_attempts=0,
        import_path=hammer.import_path,
        mimer_timeout=hammer.mimer_timeout,
    )

    result = close_gap(
        agda_file=agda_file,
        source=source,
        gap=gap,
        llm=None,
        config=config,
        mimer_hints=list(mimer_hints) + [lemma_name],
        target_name=target_name,
        verbose=verbose,
    )

    log.event(
        "promote", hole_index=gap.hole_index, lemma=lemma_name,
        signature=signature, ok=result.success, solution=result.solution,
    )

    if result.success:
        result.method = f"lemma:{lemma_name} :: {signature}"
    else:
        restore_file(helpers_file, saved_helpers)

    return result


def _lemma_from_method(result: GapResult) -> ProofObligation:
    payload = result.method.split("lemma:", 1)[1]
    name, signature = payload.split(" :: ", 1)

    return ProofObligation(
        name=name.strip(),
        signature=signature.strip(),
        informal_hint=result.gap.informal_hint,
    )


def _fresh_lemma_name(
    target_name: str,
    hole_index: int,
    existing: list[ProofObligation],
) -> str:
    base = "".join(char for char in target_name if char.isalnum()) or "lemma"
    taken = {lemma.name for lemma in existing}

    candidate = f"{base}-gap{hole_index}"
    suffix = 0

    while candidate in taken:
        suffix += 1
        candidate = f"{base}-gap{hole_index}-{suffix}"

    return candidate


def _declaration_of(result: DSPResult, obligation: ProofObligation) -> str:
    """
    Pull the proved lemma's declaration out of the temporary helper-goal file
    contents that the recursive call returned.
    """

    if result.final_source is None:
        raise ValueError(f"Lemma {obligation.name} succeeded without a source.")

    lines = result.final_source.splitlines()
    start = None

    for index, line in enumerate(lines):
        if line.startswith(f"{obligation.name} :"):
            start = index
            break

    if start is None:
        raise ValueError(
            f"Could not find declaration of {obligation.name} in the proved file."
        )

    end = len(lines)

    for index in range(start + 1, len(lines)):
        line = lines[index]

        if line and not line.startswith((" ", "\t", "--")) and " : " in line:
            end = index
            break

    return "\n".join(lines[start:end]).strip()
