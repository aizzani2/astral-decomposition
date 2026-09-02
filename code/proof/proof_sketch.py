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
"""

from __future__ import annotations

from pathlib import Path
import re

from core.agda_client import check_sketch, run_plain_agda
from core.config import (
    DEFAULT_MODEL,
    GAP_LLM_ATTEMPTS,
    MAX_DEPTH,
    SKETCH_MAX_ATTEMPTS,
    AGDA_ROOT,
)
from core.hammer import HammerConfig, close_gap
from core.llm_client import ProofLLM, parse_informal_steps
from core.proof_context import get_signature_line, infer_target_name_from_first_hole
from core.proof_files import (
    preserved_file,
    append_helper_declaration,
    reset_helpers_file,
    restore_file,
    save_file,
    write_helper_goal_file,
    write_postulated_helpers_file,
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
from util.sketch_ops import (
    available_names,
    available_signatures,
    build_gaps,
    count_holes,
    replace_hole,
    context_signatures,
)
from util.source_edit import ensure_import, replace_top_level_decl


HELPERS_IMPORT = "open import Tests.Helpers"
HELPERS_MODULE = "Tests.Helpers"
CONTEXT_MODULE = "Tests.Context"

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

    indent = "  " * depth

    if depth > max_depth:
        return DSPResult(
            success=False,
            target_name="<max-depth>",
            output=f"Maximum recursion depth exceeded: {max_depth}",
        )

    original_source = save_file(agda_file)
    original_helpers = save_file(helpers_file)

    if original_source is None:
        return DSPResult(
            success=False,
            target_name="<unknown>",
            output=f"File does not exist: {agda_file}",
        )

    try:
        target_name, _goal, _load = infer_target_name_from_first_hole(agda_file)
    except ValueError as error:
        return DSPResult(success=False, target_name="<unknown>", output=str(error))

    signature_line = get_signature_line(original_source, target_name)

    if verbose:
        print(f"\n{indent}=== DSP on {target_name} (depth {depth}) ===")

    # ---------------------------------------------------------------- draft
    informal = _get_informal_proof(
        llm=llm,
        informal_statement=informal_statement,
        informal_proof_text=informal_proof_text,
        signature_line=signature_line,
        verbose=verbose,
        indent=indent,
    )

    if informal is None:
        restore_file(agda_file, original_source)
        return DSPResult(
            success=False,
            target_name=target_name,
            output="Could not obtain a usable informal proof draft.",
        )

    if verbose:
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

        return DSPResult(
            success=False,
            target_name=target_name,
            informal=informal,
            output="Sketch stage failed:\n" + "\n\n".join(sketch_errors[-2:]),
        )

    if verbose:
        print(
            f"{indent}Sketch accepted: {len(sketch.gaps)} gap(s), "
            f"{len(sketch.lemmas)} lemma(s)."
        )

    # ---------------------------------------------------------------- prove
    names = available_signatures(
        sketch.source,
        context_signatures(AGDA_ROOT, exclude=frozenset({"Target", "HelperGoal"})),
    )
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

        return DSPResult(
            success=False,
            target_name=target_name,
            informal=informal,
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

        return DSPResult(
            success=False,
            target_name=target_name,
            informal=informal,
            sketch=sketch,
            gap_results=gap_results,
            output="Holes remain in the completed proof; sketch/goal mismatch.",
        )

    # ------------------------------------------------------ discharge lemmas
    obligations = sketch.lemmas + promoted
    lemma_results: list[DSPResult] = []

    if obligations:
        reset_helpers_file(helpers_file)

        for obligation in obligations:
            if verbose:
                print(f"{indent}  discharging lemma {obligation.name}")

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

            if not lemma_result.success:
                restore_file(agda_file, original_source)
                restore_file(helpers_file, original_helpers)

                return DSPResult(
                    success=False,
                    target_name=target_name,
                    informal=informal,
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

        return DSPResult(
            success=False,
            target_name=target_name,
            informal=informal,
            sketch=sketch,
            gap_results=gap_results,
            lemma_results=lemma_results,
            output=message,
        )

    return DSPResult(
        success=True,
        target_name=target_name,
        informal=informal,
        sketch=sketch,
        gap_results=gap_results,
        lemma_results=lemma_results,
        final_source=working_source,
        output=final.output,
    )


# ---------------------------------------------------------------------------
# Stage helpers
# ---------------------------------------------------------------------------


def _get_informal_proof(
    llm: ProofLLM,
    informal_statement: str | None,
    informal_proof_text: str | None,
    signature_line: str,
    verbose: bool,
    indent: str,
) -> InformalProof | None:
    statement = informal_statement or (
        f"Prove the following statement, given in Agda notation:\n{signature_line}"
    )

    if informal_proof_text:
        try:
            steps = parse_informal_steps(informal_proof_text)
        except ValueError:
            return None

        return InformalProof(
            statement=statement,
            steps=steps,
            raw=informal_proof_text,
        )

    if verbose:
        print(f"{indent}Drafting informal proof...")

    try:
        return llm.draft_informal_proof(
            informal_statement=statement,
            formal_signature=signature_line,
        )
    except (ValueError, RuntimeError):
        return None


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

    errors: list[str] = []
    previous_errors = history.messages_for_target(target_name)

    for attempt in range(1, max_attempts + 1):
        if verbose:
            print(f"{indent}Sketch attempt {attempt}...")

        try:
            lemmas, sketch_text, raw = llm.sketch(
                source=original_source,
                target_name=target_name,
                signature=signature_line,
                informal=informal,
                available_names=available_names(original_source),
                previous_errors=previous_errors,
                helpers_module=HELPERS_MODULE,
                context_module=CONTEXT_MODULE,
            )
        except (ValueError, RuntimeError) as error:
            errors.append(str(error))
            previous_errors = previous_errors + [f"Parse failure: {error}"]
            continue

        first_line = sketch_text.strip().splitlines()[0].strip()

        if first_line != signature_line.strip():
            message = (
                "The sketch changed the target type signature.\n"
                f"Expected: {signature_line}\nGot:      {first_line}"
            )
            errors.append(message)
            previous_errors = previous_errors + [message]
            continue

        if count_holes(sketch_text) == 0:
            # Not fatal: a hole-free sketch is just a direct proof attempt.
            if verbose:
                print(f"{indent}  (sketch has no holes; treating as a direct proof)")

        write_postulated_helpers_file(helpers_file=helpers_file, helpers=lemmas)

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
            errors.append(check.message)
            previous_errors = history.messages_for_target(target_name)
            continue

        gaps = build_gaps(trial, check.goals)

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

    return None, errors

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
    verbose: bool,
    indent: str,
) -> GapResult:
    """
    Last resort for a stuck hole: abstract it into a top-level lemma, postulate
    the lemma, and apply it to the in-scope variables. The lemma then has to be
    proved recursively, which is how the paper's "hard step becomes its own
    lemma" idea shows up here.
    """

    lemma_name = _fresh_lemma_name(target_name, gap.hole_index, existing_lemmas)

    if verbose:
        print(f"{indent}  promoting gap {gap.hole_index} to lemma {lemma_name}")

    try:
        signature = llm.lemma_signature_for_gap(
            lemma_name=lemma_name,
            goal_type=gap.goal_type,
            context=gap.context,
            context_module=CONTEXT_MODULE,
        )
    except (ValueError, RuntimeError) as error:
        return GapResult(success=False, gap=gap, method="failed", output=str(error))

    if _is_degenerate(signature, gap.goal_type):
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
    append_helper_declaration(
        helpers_file,
        f"postulate\n  {lemma_name} : {signature}",
    )

    variables = [entry.name for entry in gap.context if entry.in_scope]
    candidates = [lemma_name] + [
        f"{lemma_name} {' '.join(variables[:k])}"
        for k in range(len(variables), 0, -1)
    ]

    config = HammerConfig(
        tactics=tuple(candidates),
        use_mimer=False,
        llm_attempts=0,
        import_path=hammer.import_path,
    )

    result = close_gap(
        agda_file=agda_file,
        source=source,
        gap=gap,
        llm=None,
        config=config,
        verbose=verbose,
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
