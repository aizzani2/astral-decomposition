"""
Closing individual holes: the "Prove" stage.

Agda has no Sledgehammer, so this plays the same role with what Agda does
have, in increasing order of cost:

    1. a fixed list of cheap candidate terms (refl, ...), mirroring the
       paper's "Sledgehammer + heuristics" baseline where stock tactics are
       tried before the expensive tool;
    2. Agda's own automated prover (Mimer) via `Cmd_autoOne`, *with every
       lemma in scope passed as a hint*. Bare Mimer only uses local variables
       and constructors; hinted Mimer closes e.g.
       `trans (cong suc (addComm n m)) (sym (plusSucRight m n))` in a second;
    3. the language model, with the goal type, the local context, and the
       informal step the hole came from.

A candidate is accepted only if splicing it in leaves the file typechecking
and removes exactly that hole. That check goes through `check_sketch`, not
plain `agda`, because the file legitimately still contains other holes.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

from core.config import AGDA_IMPORT_PATH, MIMER_TIMEOUT_SECONDS
from core.agda_client import AgdaSession, AutoError, check_sketch
from core.llm_client import ProofLLM
from core.proof_state import GapResult, SketchGap
from core.run_log import run_logger
from util.sketch_ops import count_holes, excerpt_around_hole, replace_hole


# Cheap first-pass candidates. Deliberately small: each one costs a full Agda
# load. Extend per project rather than making this list open-ended.
DEFAULT_TACTICS: tuple[str, ...] = (
    "refl",
)
BAD_TERM = re.compile(r"(?:^|[\s(])[_?](?:[\s)]|$)")


@dataclass
class HammerConfig:
    tactics: tuple[str, ...] = DEFAULT_TACTICS
    use_mimer: bool = True
    mimer_timeout: int = MIMER_TIMEOUT_SECONDS
    mimer_candidates: int = 10   # how many of Mimer's listed solutions to typecheck
    llm_attempts: int = 2
    import_path: str = AGDA_IMPORT_PATH
    extra_tactics: list[str] = field(default_factory=list)

    def all_tactics(self) -> list[str]:
        return list(self.tactics) + list(self.extra_tactics)


def close_gap(
    agda_file: Path,
    source: str,
    gap: SketchGap,
    llm: ProofLLM | None = None,
    config: HammerConfig | None = None,
    available_names: str = "",
    mimer_hints: list[str] | None = None,
    target_name: str = "",
    verbose: bool = True,
) -> GapResult:
    """
    Try to close one hole in `source`. Does not mutate `agda_file` on failure:
    the caller owns the file contents and gets the winning term back.

    `mimer_hints` are names Mimer may apply (lemmas, `sym`, `trans`, ...). They
    must all be in scope in `agda_file` or Agda rejects the whole command.
    """

    config = config or HammerConfig()
    baseline_holes = count_holes(source)
    log = run_logger()

    log.event(
        "gap_start",
        hole_index=gap.hole_index,
        goal_id=gap.goal_id,
        goal_type=gap.goal_type,
        context=gap.context,
        informal_hint=gap.informal_hint,
        n_holes=baseline_holes,
    )

    def attempt(term: str, method: str) -> GapResult | None:
        if not _is_admissible(term):
            log.event(
                "gap_candidate", hole_index=gap.hole_index, method=method,
                term=term, ok=False, output="inadmissible",
            )
            return GapResult(
                success=False, gap=gap, method=method,
                output=f"Inadmissible term: {term!r}",
            )
        ok, output = _candidate_typechecks(
            agda_file=agda_file,
            source=source,
            gap=gap,
            term=term,
            baseline_holes=baseline_holes,
            import_path=config.import_path,
        )

        log.event(
            "gap_candidate", hole_index=gap.hole_index, method=method,
            term=term, ok=ok, output=output,
        )

        if verbose:
            status = "ok" if ok else "rejected"
            print(f"    [{method}] {term!r} -> {status}")

        if ok:
            return GapResult(success=True, gap=gap, solution=term, method=method)

        return GapResult(success=False, gap=gap, method=method, output=output)

    def done(result: GapResult) -> GapResult:
        log.event(
            "gap_result",
            hole_index=gap.hole_index,
            goal_type=gap.goal_type,
            success=result.success,
            method=result.method,
            solution=result.solution,
            output=result.output,
        )
        return result

    failures: list[str] = []

    # 1. cheap tactics
    for tactic in config.all_tactics():
        result = attempt(tactic, f"tactic:{tactic}")
        if result and result.success:
            return done(result)
        if result:
            failures.append(f"{tactic}: {_first_lines(result.output)}")

    # 2. Agda's own automation, hinted with everything in scope. Mimer does
    #    not run the termination checker, so take its candidate list and keep
    #    going until one survives a real typecheck.
    if config.use_mimer and gap.goal_id is not None:
        terms, note = _try_mimer(
            agda_file, gap.goal_id, config.import_path,
            hints=mimer_hints or [], timeout=config.mimer_timeout,
        )

        log.event(
            "mimer", hole_index=gap.hole_index, goal_id=gap.goal_id,
            hints=mimer_hints or [], terms=terms, note=note,
        )

        if verbose and not terms:
            print(f"    [mimer] no solution ({note})")

        for rank, term in enumerate(terms[: config.mimer_candidates]):
            result = attempt(term, "mimer" if rank == 0 else f"mimer#{rank}")

            if result and result.success:
                return done(result)

            if result:
                failures.append(f"mimer ({term}): {_first_lines(result.output)}")

    # 3. the model
    if llm is not None:
        previous: list[str] = []

        for attempt_index in range(config.llm_attempts):
            try:
                term = llm.fill_gap(
                    goal_type=gap.goal_type,
                    context=gap.context,
                    informal_hint=gap.informal_hint,
                    excerpt=excerpt_around_hole(source, gap.hole_index),
                    available_names=available_names,
                    previous_errors=previous,
                    target_name=target_name,
                    attempt=attempt_index,
                )
            except (ValueError, RuntimeError) as error:
                previous.append(str(error))
                failures.append(f"llm: {error}")
                continue

            result = attempt(term, "llm")

            if result and result.success:
                return done(result)

            if result:
                previous.append(
                    f"You proposed:\n{term}\n\nAgda rejected it:\n{result.output}"
                )
                failures.append(f"llm ({term}): {_first_lines(result.output)}")

    return done(GapResult(
        success=False,
        gap=gap,
        method="failed",
        output="No candidate closed the hole.\n" + "\n".join(failures[-6:]),
    ))


def _candidate_typechecks(
    agda_file: Path,
    source: str,
    gap: SketchGap,
    term: str,
    baseline_holes: int,
    import_path: str,
) -> tuple[bool, str]:
    """
    Splice `term` into the hole, typecheck, and restore the file.

    Success means: no type errors, and one fewer hole than we started with.
    Other holes are allowed to remain; that is what makes this a sketch.
    """

    original = agda_file.read_text() if agda_file.exists() else None

    try:
        candidate_source = replace_hole(source, gap.hole_index, term)
    except IndexError as error:
        return False, str(error)

    remaining = count_holes(candidate_source)

    if remaining != baseline_holes - 1:
        return False, (
            f"Term did not close exactly one hole "
            f"({baseline_holes} -> {remaining})."
        )

    agda_file.write_text(candidate_source)

    try:
        result = check_sketch(agda_file, import_path=import_path, with_context=False)
    finally:
        if original is not None:
            agda_file.write_text(original)

    if result.kind == "error":
        return False, result.message

    return True, ""


def _try_mimer(
    agda_file: Path,
    goal_id: int,
    import_path: str,
    hints: list[str],
    timeout: int,
) -> tuple[list[str], str]:
    """Returns (candidate terms best-first, note explaining an empty list)."""

    try:
        with AgdaSession(agda_file, import_path=import_path) as session:
            load = session.load()

            if load.kind != "goal":
                return [], f"file did not load with goals ({load.kind})"

            try:
                terms = session.auto_list(goal_id, hints=hints, timeout=timeout)
            except AutoError as error:
                # Usually an out-of-scope hint. Retry with no hints so a bad
                # name never costs us the whole hammer step.
                if not hints:
                    return [], f"auto error: {error}"

                terms = session.auto_list(goal_id, hints=[], timeout=timeout)
                return terms, f"hints rejected ({_first_lines(str(error), 2)}); retried bare"

            return terms, "ok" if terms else "no solution"
    except Exception as error:
        # Mimer/Agsy availability and the exact JSON shape vary by Agda
        # version; never let that take down the pipeline.
        return [], f"{type(error).__name__}: {error}"


def _first_lines(text: str, n: int = 6) -> str:
    lines = [line for line in text.splitlines() if line.strip()]
    return "\n".join(lines[:n])


def _is_admissible(term: str) -> bool:
    return bool(term.strip()) and not (
        BAD_TERM.search(term) or "{!" in term
    )
