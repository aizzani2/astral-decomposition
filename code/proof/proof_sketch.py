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

Lemma discipline (proof/layout.py keeps the lemmas, above the theorem in
its own file):

    * Proved lemma declarations accumulate, one at a time as they are
      discharged.
    * While a sketch is being checked and its gaps closed, the lemmas it
      declares are postulated. Those postulates are dropped (by restoring the
      snapshot taken at entry) before the lemmas are proved, so nothing is
      ever proved from an unproved assumption.
    * A nested lemma's run never discards the sibling lemmas its parent has
      already proved: the parent's final check depends on them.
"""

from __future__ import annotations

from contextlib import contextmanager
from pathlib import Path
import re

from core.agda_client import AgdaSession, check_sketch, run_plain_agda
from core.config import (
    DEFAULT_MODEL,
    MIMER_BASE_HINTS,
    GAP_LLM_ATTEMPTS,
    DRAFT_SAMPLES,
    MAX_DEPTH,
    SKETCH_MAX_ATTEMPTS,
)
from core.hammer import HammerConfig, close_gap
from core.llm_client import ProofLLM, parse_informal_steps
from core.proof_files import preserved_file, restore_file, save_file
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
from proof.holes import model_names, place_holes as place_holes_in
from proof.layout import Layout
from util.agda_source import declaration_span, get_signature_line
from util.deproof import Decomposition, decompose
from util.sketch_ops import (
    HOLE_RE,
    available_signatures,
    build_gaps,
    count_holes,
    hint_names,
    replace_hole,
)


# A name as Agda source spells it (operators and Unicode included).
NAME_RE = re.compile(r"[^\s(){};]+")


def prove_dsp(agda_file: Path, name: str, line: int | None = None, **kwargs) -> DSPResult:
    """
    Prove `name` in `agda_file`, a file of an Agda project: in practice a
    mirror of a library checkout (util/checkout.py), since the file is
    rewritten while the proof is built. It is cut after the theorem, whose
    proof becomes one hole, and lemmas go just above it (proof/layout.py).
    `line` picks the declaration when the name occurs more than once. The
    file is restored on the way out.
    """

    with preserved_file(agda_file):
        layout = Layout(agda_file, name, line)
        return _prove_dsp(agda_file, layout, target_name=name, **kwargs)


def _prove_dsp(
    agda_file: Path,
    layout: Layout,
    informal_statement: str | None = None,
    informal_proof_text: str | None = None,
    llm: ProofLLM | None = None,
    model: str = DEFAULT_MODEL,
    depth: int = 0,
    draft_samples: int = DRAFT_SAMPLES,
    draft: bool = True,
    target_name: str = "",
    **kwargs,
) -> DSPResult:
    llm = llm or ProofLLM(model=model)
    log = run_logger()

    source = save_file(agda_file)

    if source is None:
        return DSPResult(
            success=False, target_name="<unknown>",
            output=f"File does not exist: {agda_file}",
        )

    signature_line = get_signature_line(source, target_name)
    statement = informal_statement or (
        f"Prove the following statement, given in Agda notation:\n{signature_line}"
    )

    with log.scope(target=target_name, depth=depth):
        # No drafting at all: the sketch is written from the statement alone
        # (an ablation; recursive lemmas are then not drafted either).
        if not draft:
            drafts = [InformalProof(statement=statement, steps=[], raw="")]
        # A human-written proof skips drafting entirely.
        elif informal_proof_text:
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

        for draft_index, informal_draft in enumerate(drafts):
            with log.scope(draft_index=draft_index):
                result = _attempt_dsp(
                    agda_file=agda_file,
                    layout=layout,
                    informal=informal_draft,
                    target_name=target_name,
                    signature_line=signature_line,
                    llm=llm,
                    model=model,
                    depth=depth,
                    draft=draft,
                    **kwargs,
                )

            if result.success:
                return result

            last = result
            restore_file(agda_file, source)

        return last


def _attempt_dsp(
    agda_file: Path,
    layout: Layout,
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
    place_holes: bool = False,
    draft: bool = True,
) -> DSPResult:
    llm = llm or ProofLLM(model=model)
    history = history or ProofHistory()
    hammer = hammer or HammerConfig(llm_attempts=GAP_LLM_ATTEMPTS)
    log = run_logger()

    indent = "  " * depth

    def fail(stage: str, **fields) -> DSPResult:
        result = DSPResult(
            success=False, target_name=target_name, informal=informal, stage=stage, **fields
        )
        log.event("dsp_result", success=False, stage=stage, output=result.output)
        return result

    if depth > max_depth:
        return fail("depth", output=f"Maximum recursion depth exceeded: {max_depth}")

    original_source = save_file(agda_file)
    original_helpers = layout.snapshot()

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
        layout=layout,
        original_source=original_source,
        target_name=target_name,
        signature_line=signature_line,
        informal=informal,
        llm=llm,
        max_attempts=sketch_max_attempts,
        history=history,
        hammer=hammer,
        place_holes=place_holes,
        verbose=verbose,
        indent=indent,
    )

    if sketch is None:
        restore_file(agda_file, original_source)
        layout.restore(original_helpers)

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
    lemmas_now = layout.text()

    names = available_signatures(sketch.source, lemmas_now)

    # Mimer hints: the run's lemmas. Mimer already tries recursive calls by
    # itself, and naming the function under definition as a hint makes the
    # search blow up (5s -> no solution on a gap it otherwise closes in under
    # a second), so the rest of the file is not offered wholesale.
    hints = list(MIMER_BASE_HINTS) + [n for n in hint_names(lemmas_now) if n not in MIMER_BASE_HINTS]
    # Names the sketch's author used are good hints too (a wrong attempt
    # usually still reaches for the right lemmas); out-of-scope ones are
    # dropped by the hammer when Agda rejects them.
    hints += [n for n in model_names(sketch.raw_response, target_name) if n not in hints]

    log.event("prove_start", n_gaps=len(sketch.gaps), mimer_hints=hints)

    working_source = sketch.source
    gap_results: list[GapResult] = []
    promoted: list[ProofObligation] = []
    failed: list[GapResult] = []

    # One Agda session for the whole sketch: candidates are given to their
    # holes instead of reloading the file for each (core/hammer.py).
    with _sketch_session(agda_file, hammer) as session:
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
                session=session,
            )

            if not result.success:
                result = _promote_gap_to_lemma(
                    agda_file=agda_file,
                    layout=layout,
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
                    session=session,
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

            if result.method.startswith("lemma:"):
                # the new lemma's postulate belongs in the text from now on
                working_source = layout.render(working_source)

    if failed:
        restore_file(agda_file, original_source)
        layout.restore(original_helpers)

        return fail(
            "gaps",
            sketch=sketch,
            gap_results=gap_results,
            output="\n\n".join(
                f"Gap {r.gap.hole_index} ({r.gap.goal_type}):\n{r.output}"
                for r in failed
            ),
        )

    agda_file.write_text(layout.render(working_source))

    if count_holes(working_source) != 0:
        restore_file(agda_file, original_source)
        layout.restore(original_helpers)

        return fail(
            "gaps",
            sketch=sketch,
            gap_results=gap_results,
            output="Holes remain in the completed proof; sketch/goal mismatch.",
        )

    # ------------------------------------------------------ discharge lemmas
    # Only lemmas the proof uses are part of the decomposition: a model that
    # names a lemma and then proves the theorem without it has not split the
    # proof there, and an unused lemma must not sink a finished proof.
    declared = sketch.lemmas + promoted
    used_names = _names_in_declaration(working_source, target_name)
    obligations = [o for o in declared if o.name in used_names]
    unused = [o.name for o in declared if o.name not in used_names]
    lemma_results: list[DSPResult] = []

    if unused:
        log.event("lemma_unused", lemmas=unused)

    if declared:
        # Drop this level's postulates; keep everything proved so far.
        layout.restore(original_helpers)

    for obligation in obligations:
        if verbose:
            print(f"{indent}  discharging lemma {obligation.name}")

        log.event(
            "lemma_start", lemma=obligation.name,
            signature=obligation.signature, hint=obligation.informal_hint,
        )

        layout.lemma_goal(obligation)

        with preserved_file(agda_file):
            lemma_result = _prove_dsp(
                agda_file,
                layout,
                target_name=obligation.name,
                informal_statement=obligation.informal_hint or None,
                llm=llm,
                model=model,
                sketch_max_attempts=sketch_max_attempts,
                hammer=hammer,
                max_depth=max_depth,
                depth=depth + 1,
                history=history,
                verbose=verbose,
                place_holes=place_holes,
                draft=draft,
            )

        lemma_results.append(lemma_result)

        log.event(
            "lemma_end", lemma=obligation.name,
            success=lemma_result.success, output=lemma_result.output,
        )

        if not lemma_result.success:
            restore_file(agda_file, original_source)
            layout.restore(original_helpers)

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

        if lemma_result.final_source is None:
            raise ValueError(f"Lemma {obligation.name} succeeded without a source.")

        layout.add_proved(layout.declaration_of(lemma_result.final_source, obligation.name))

    # ----------------------------------------------------------- final check
    working_source = layout.render(working_source)
    agda_file.write_text(working_source)
    final = run_plain_agda(agda_file, import_path=hammer.import_path, timeout=hammer.agda_timeout)

    leftover_postulates = layout.has_postulates()

    if not final.success or leftover_postulates:
        restore_file(agda_file, original_source)
        layout.restore(original_helpers)

        message = final.output

        if leftover_postulates:
            message += "\n\nSome lemmas are still postulated."

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
        stage="done",
        decomposition=log_decomposition(agda_file, target_name, hammer.import_path),
    )

    log.event(
        "dsp_result", success=True, stage="done",
        final_source=working_source,
        lemmas_source=layout.text(),
        gap_methods=[r.method for r in gap_results],
    )

    return result


# ---------------------------------------------------------------------------
# Stage helpers
# ---------------------------------------------------------------------------

def log_decomposition(
    agda_file: Path,
    target_name: str,
    import_path: str,
    role: str = "proof",
    declared: list[str] | None = None,
) -> Decomposition | None:
    """
    Take a proof apart into clauses, steps and lemmas (util.deproof) and log
    it. `role` is "proof" (finished), "sketch" (holes still open; `declared`
    are its lemma signatures) or "reference". This is analysis, so a failure
    here is logged, never raised.
    """

    log = run_logger()

    try:
        decomposition = decompose(
            agda_file, target_name, import_path=import_path, declared=declared or ()
        )
    except Exception as error:
        log.event(
            "decomposition", role=role, name=target_name, ok=False,
            error=f"{type(error).__name__}: {error}",
        )
        return None

    log.event(
        "decomposition", role=role, name=target_name, ok=True,
        decomposition=decomposition, text=decomposition.render(),
    )

    return decomposition


def _build_sketch(
    agda_file: Path,
    layout: Layout,
    original_source: str,
    target_name: str,
    signature_line: str,
    informal: InformalProof,
    llm: ProofLLM,
    max_attempts: int,
    history: ProofHistory,
    hammer: HammerConfig,
    verbose: bool,
    indent: str,
    place_holes: bool = False,
) -> tuple[FormalSketch | None, list[str]]:
    """
    Ask for a skeleton until one typechecks with holes.

    The success condition here is *not* a complete proof: it is "Agda accepts
    the structure and reports N interaction points".

    Two repairs before giving up on a sketch, each logged as `sketch_repair`:
    a declared lemma whose statement does not check is dropped; and, with
    `place_holes`, holes go where the sketch's proof fails (proof/holes.py),
    for a model that writes whole proofs rather than skeletons.
    """

    log = run_logger()
    errors: list[str] = []
    previous_errors = history.messages_for_target(target_name)
    helpers_snapshot = layout.snapshot()
    import_path = hammer.import_path
    names = available_signatures(layout.text())

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
                attempt=attempt,
            )
        except (ValueError, RuntimeError) as error:
            reject("parse", str(error))
            previous_errors = previous_errors + [f"Parse failure: {error}"]
            continue

        first_line = _sketch_signature(sketch_text, target_name)

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
        def install(lemmas: list[ProofObligation], text: str):
            layout.restore(helpers_snapshot)
            layout.postulate(lemmas, before=target_name)
            trial = layout.install(text)
            agda_file.write_text(trial)
            return trial, check_sketch(
                agda_file, import_path=import_path, with_context=True, timeout=hammer.agda_timeout,
            )

        trial, check = install(lemmas, sketch_text)
        repairs: list[str] = []

        # Two repairs, in turn until neither helps (one error can hide the
        # other: Agda stops at a clause's parse error before a lemma's):
        # a lemma whose statement does not check sinks the whole sketch, so
        # drop it and see whether the rest stands; and a sketch that is really
        # a whole proof attempt keeps what checks, with holes where it fails.
        for _round in range(len(lemmas) + 2):
            if check.kind != "error":
                break

            bad = layout.lemma_at_error(check.message, lemmas) if lemmas else None

            if bad is not None:
                lemmas = [lemma for lemma in lemmas if lemma.name != bad]
                repairs.append(f"dropped lemma {bad}, whose statement did not check")
                trial, check = install(lemmas, sketch_text)
                continue

            if not place_holes:
                break

            before = len(repairs)
            trial, check = place_holes_in(
                agda_file, trial, check, target_name, None, hammer, repairs,
            )

            if len(repairs) == before or not lemmas:
                break

        if repairs:
            log.event("sketch_repair", attempt=attempt, repairs=repairs,
                      accepted=check.kind != "error")

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

        # A hole of function type means a clause left arguments unbound
        # (`f (suc m) = {!!}` for a two-argument f, or a point-free clause).
        # Mimer is poor at introducing binders, so let Agda introduce them
        # (refine/intro: `λ { x → {!!} }`) until the holes are propositions.
        if any(_is_function_type(g.type) for g in check.goals):
            trial, check, introduced = _introduce_binders(agda_file, trial, check, hammer)
            if introduced:
                log.event("sketch_repair", attempt=attempt, accepted=check.kind != "error",
                          repairs=[f"introduced binders in {introduced} function-typed hole(s)"])

        unbound = [g.type for g in check.goals if _is_function_type(g.type)]

        if unbound:
            message = (
                "Some clauses do not bind all arguments of the function, so their "
                "holes have function types:\n  " + "\n  ".join(unbound) +
                "\nWrite every argument on the left-hand side of each clause "
                "(pattern matching where the informal proof does induction) so "
                "that each hole is an equation, not a function."
            )
            history.add(
                phase="sketch", target_name=target_name,
                candidate=sketch_text, agda_output=message,
            )
            reject("unbound_args", message, sketch=sketch_text, lemmas=lemmas, raw=raw)
            previous_errors = history.messages_for_target(target_name)
            continue

        gaps = build_gaps(trial, check.goals)
        decomposition = log_decomposition(
            agda_file, target_name, import_path, role="sketch",
            declared=[lemma.name for lemma in lemmas],
        )

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
                decomposition=decomposition,
            ),
            errors,
        )

    layout.restore(helpers_snapshot)
    return None, errors


def _introduce_binders(agda_file: Path, trial: str, check, hammer: HammerConfig, limit: int = 8):
    """
    Agda's refine/intro on each function-typed hole, one at a time from the
    last, until none is left (or intro fails). Returns the new text, its
    check, and how many binders were introduced.
    """

    introduced = 0

    for _ in range(limit):
        if check.kind == "error":
            break

        holes = [g for g in check.goals if _is_function_type(g.type) and g.id is not None]

        if not holes:
            break

        goal = max(holes, key=lambda g: g.id)
        index = sorted(g.id for g in check.goals if g.id is not None).index(goal.id)

        with AgdaSession(agda_file, import_path=hammer.import_path, timeout=hammer.agda_timeout) as session:
            if session.load().kind != "goal":
                break
            text = session.intro(goal.id)

        if not text:
            break

        # Agda writes the new holes as `?`
        text = HOLE_RE.sub("{!!}", text)
        candidate = replace_hole(trial, index, text)
        agda_file.write_text(candidate)
        result = check_sketch(agda_file, import_path=hammer.import_path, with_context=True,
                              timeout=hammer.agda_timeout)

        if result.kind == "error":
            agda_file.write_text(trial)
            break

        trial, check = candidate, result
        introduced += 1

    return trial, check, introduced


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


def _is_function_type(goal_type: str) -> bool:
    """True if the goal has an arrow at nesting depth 0 (a Π-type)."""

    depth = 0

    for char in goal_type:
        if char in "({[":
            depth += 1
        elif char in ")}]":
            depth = max(0, depth - 1)
        elif char == "→" and depth == 0:
            return True

    return "->" in _strip_brackets(goal_type) or goal_type.lstrip().startswith("∀")


def _strip_brackets(text: str) -> str:
    out: list[str] = []
    depth = 0

    for char in text:
        if char in "({[":
            depth += 1
        elif char in ")}]":
            depth = max(0, depth - 1)
        elif depth == 0:
            out.append(char)

    return "".join(out)


def _sketch_signature(text: str, name: str) -> str:
    """
    The sketch's signature for `name`, its continuation lines joined: the
    first code line and the indented lines after it.
    """

    lines = [line for line in text.splitlines() if line.strip() and not line.strip().startswith("--")]

    if not lines:
        return ""

    parts = [lines[0].strip()]
    column = len(lines[0]) - len(lines[0].lstrip())

    for line in lines[1:]:
        if len(line) - len(line.lstrip()) <= column:
            break
        parts.append(line.strip())

    return " ".join(parts)


def _normalise(line: str) -> str:
    return " ".join(line.replace("->", "→").split())


def _plausible_signature(signature: str) -> bool:
    """Cheap filter for prompt echoes and prose before Agda sees the text."""

    if not signature or "\n" in signature or len(signature) > 1500:
        return False

    if re.search(r"</?[A-Z_]+>|```", signature):
        return False

    return "→" in signature or "->" in signature or "≡" in signature or "==" in signature


def _is_degenerate(signature: str, goal_type: str) -> bool:
    """A lemma that just restates the goal buys nothing and recurses forever."""
    def norm(s: str) -> str:
        s = re.sub(r"∀\s*[^→]*→", "", s)
        s = re.sub(r"\([^:()]+:[^()]+\)\s*→", "", s)       # (x : A) →
        s = re.sub(r"\{[^:{}]+:[^{}]+\}\s*→", "", s)       # {x : A} →, implicit binders too
        return " ".join(s.split())
    return norm(signature) == norm(goal_type)


def _names_in_declaration(source: str, name: str) -> set[str]:
    """Every word in `name`'s declaration (signature and clauses)."""

    try:
        start, _, end, _ = declaration_span(source, name)
    except ValueError:
        return set(NAME_RE.findall(source))

    return set(NAME_RE.findall(source[start:end]))


def _promote_gap_to_lemma(
    agda_file: Path,
    layout: Layout,
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
    session=None,
) -> GapResult:
    """
    Last resort for a stuck hole: abstract it into a top-level lemma, postulate
    the lemma, and apply it to the in-scope variables. The lemma then has to be
    proved recursively, which is how the paper's "hard step becomes its own
    lemma" idea shows up here.
    """

    log = run_logger()
    lemma_name = _fresh_lemma_name(target_name, gap.hole_index, existing_lemmas, source)

    if verbose:
        print(f"{indent}  promoting gap {gap.hole_index} to lemma {lemma_name}")

    # The goal and context as written (not normalised, which unfolds into
    # names the file never imported), from the open session when there is one.
    goal_type, context = gap.goal_type, gap.context
    if session is not None and session.alive and gap.goal_id is not None:
        try:
            goal_type, context = session.goal_type_and_context(gap.goal_id, "AsIs")
            goal_type = goal_type or gap.goal_type
        except Exception:
            goal_type, context = gap.goal_type, gap.context

    try:
        signature = llm.lemma_signature_for_gap(
            lemma_name=lemma_name,
            goal_type=goal_type,
            context=context,
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

    if _is_degenerate(signature, goal_type):
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

    # Add rather than rewrite: the parent may already have proved sibling
    # lemmas that its final check depends on.
    saved_helpers = layout.snapshot()
    layout.postulate([obligation], before=target_name)
    rendered = layout.render(source)
    agda_file.write_text(rendered)
    _reload(session)

    variables = [entry.name for entry in context if entry.in_scope]
    # The lemma applied to its own explicit binders first, then to prefixes
    # of the in-scope variables.
    binders = [
        name for group in re.findall(r"\(([^():]+?)\s*:", signature) for name in group.split()
    ]
    exact = [name for name in binders if name in variables]
    candidates = list(dict.fromkeys(
        ([f"{lemma_name} {' '.join(exact)}"] if exact else [])
        + [lemma_name]
        + [f"{lemma_name} {' '.join(variables[:k])}" for k in range(len(variables), 0, -1)]
    ))

    config = HammerConfig(
        tactics=tuple(candidates),
        use_mimer=True,
        llm_attempts=0,
        import_path=hammer.import_path,
        mimer_timeout=hammer.mimer_timeout,
        agda_timeout=hammer.agda_timeout,
    )

    result = close_gap(
        agda_file=agda_file,
        source=rendered,
        gap=gap,
        llm=None,
        config=config,
        mimer_hints=list(mimer_hints) + [lemma_name],
        target_name=target_name,
        verbose=verbose,
        session=session,
    )

    log.event(
        "promote", hole_index=gap.hole_index, lemma=lemma_name,
        signature=signature, ok=result.success, solution=result.solution,
    )

    if result.success:
        result.method = f"lemma:{lemma_name} :: {signature}"
    else:
        layout.restore(saved_helpers)
        agda_file.write_text(layout.render(source))
        _reload(session)

    return result


@contextmanager
def _sketch_session(agda_file: Path, hammer: HammerConfig):
    """An Agda session with the sketch loaded, or None if it will not load."""

    session = AgdaSession(agda_file, import_path=hammer.import_path, timeout=hammer.agda_timeout)

    try:
        session.__enter__()
        loaded = session.load().kind == "goal"
    except Exception:
        loaded = False

    try:
        yield session if loaded else None
    finally:
        session.stop()


def _reload(session) -> None:
    """Reload a session after its file changed; a failed reload just ends it."""

    if session is None:
        return
    try:
        session.load()
    except Exception:
        session.stop()


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
    source: str = "",
) -> str:
    """`<target>-gap<i>`, avoiding other lemmas and every name in the file."""

    base = "".join(char for char in target_name if char.isalnum()) or "lemma"
    taken = {lemma.name for lemma in existing} | set(NAME_RE.findall(source))

    candidate = f"{base}-gap{hole_index}"
    suffix = 0

    while candidate in taken:
        suffix += 1
        candidate = f"{base}-gap{hole_index}-{suffix}"

    return candidate
