"""Agda-backed checks on the fixture project, including the whole DSP pipeline with a scripted model."""

from pathlib import Path

from core.agda_client import check_sketch
from core.hammer import HammerConfig
from core.llm_client import EchoBackend, ProofLLM
from core.proof_history import ProofHistory
from proof.proof_sketch import prove_dsp
from tests.conftest import needs_agda, write_target
from util.deproof import decompose
from util.sketch_export import export_sketch


@needs_agda
def test_holes_and_unsolved_metas(project: Path):
    f = write_target(project, "g : (n : Nat) → n + 0 ≡ n\ng n = {!!}")
    assert check_sketch(f, with_context=False).kind == "holes"

    f.write_text(f.read_text().replace("{!!}", "_"))
    result = check_sketch(f, with_context=False)
    assert result.kind == "error" and "Unsolved metas" in result.message


ADD_COMM = """
postulate
  plusZeroRight : (n : Nat) → n + 0 ≡ n
  plusSucRight : (m n : Nat) → m + suc n ≡ suc (m + n)

addComm : (n m : Nat) → n + m ≡ m + n
addComm zero m = sym (plusZeroRight m)
addComm (suc n) m = trans (congSuc (addComm n m)) (sym (plusSucRight m n))
"""


@needs_agda
def test_decompose_and_export_step_sketch(project: Path):
    f = write_target(project, ADD_COMM)
    before = f.read_text()
    d = decompose(f, "addComm")

    assert [len(c.steps) for c in d.clauses] == [1, 2]
    assert d.clauses[1].steps[0].recursive

    sketch = export_sketch(f, "addComm", "step", decomposition=d)
    assert sketch.valid and len(sketch.holes) == 3
    assert f.read_text() == before                       # file restored


DRAFT = """<STEP index="1" kind="induction">Induct on n.</STEP>
<STEP index="2" kind="case">Base case: 0 + 0 is 0.</STEP>
<STEP index="3" kind="case">Inductive case: use the hypothesis under suc.</STEP>
</INFORMAL_PROOF>"""

SKETCH = """</AGDA_LEMMAS>
<AGDA_SKETCH>
plusZero : (n : Nat) → n + 0 ≡ n
-- Base case: 0 + 0 is 0.
plusZero zero = {!!}
-- Inductive case: use the hypothesis under suc.
plusZero (suc n) = {!!}
"""


@needs_agda
def test_dsp_pipeline_end_to_end_with_scripted_model(project: Path):
    target = write_target(project, "plusZero : (n : Nat) → n + 0 ≡ n\nplusZero n = {!!}")
    llm = ProofLLM(backend=EchoBackend(responses=[DRAFT, SKETCH]))

    result = prove_dsp(
        target,
        "plusZero",
        llm=llm,
        draft_samples=1,
        sketch_max_attempts=1,
        hammer=HammerConfig(llm_attempts=0),
        history=ProofHistory(),
        verbose=False,
    )

    assert result.success, result.output
    assert result.stage == "done"
    assert {r.method.split(":")[0] for r in result.gap_results} <= {"tactic", "mimer"}
    assert "plusZero (suc n) = " in result.final_source


@needs_agda
def test_session_hammer_rejects_non_terminating_recursion(project: Path):
    from core.agda_client import AgdaSession
    from core.hammer import close_gap
    from util.sketch_ops import build_gaps

    f = write_target(project, "plusZero : (n : Nat) → n + 0 ≡ n\nplusZero zero = refl\nplusZero (suc n) = {!!}")
    source = f.read_text()
    check = check_sketch(f, with_context=True)
    gap = build_gaps(source, check.goals)[0]
    config = HammerConfig(
        tactics=("plusZero (suc n)", "congSuc (plusZero n)"), use_mimer=False,
        llm_attempts=0,
    )

    with AgdaSession(f) as session:
        session.load()
        result = close_gap(f, source, gap, config=config, target_name="plusZero",
                           verbose=False, session=session)

    assert result.success and result.solution == "congSuc (plusZero n)"


POINT_FREE_SKETCH = """</AGDA_LEMMAS>
<AGDA_SKETCH>
symm : {x y : Nat} → x ≡ y → y ≡ x
symm = {!!}
"""


@needs_agda
def test_function_typed_hole_gets_binders_and_no_draft(project: Path):
    target = write_target(project, "symm : {x y : Nat} → x ≡ y → y ≡ x\nsymm = {!!}")
    llm = ProofLLM(backend=EchoBackend(responses=[POINT_FREE_SKETCH]))   # no draft call

    result = prove_dsp(
        target,
        "symm",
        llm=llm,
        draft=False,
        sketch_max_attempts=1,
        hammer=HammerConfig(llm_attempts=0),
        history=ProofHistory(),
        verbose=False,
    )

    assert result.success, result.output
    assert "λ" in result.final_source                    # the binder Agda introduced


PROMOTE_SKETCH = """</AGDA_LEMMAS>
<AGDA_SKETCH>
flipEq : (n m : Nat) → suc n ≡ m → m ≡ suc n
-- flip the hypothesis
flipEq n m eq = sym {!!}
"""

LEMMA_SKETCH = """</AGDA_LEMMAS>
<AGDA_SKETCH>
flipEq-gap0 : (n m : Nat) → suc n ≡ m → suc n ≡ m
flipEq-gap0 n m eq = {!!}
"""


@needs_agda
def test_stuck_hole_promoted_to_lemma_and_proved(project: Path):
    """
    The model's term for the hole is wrong and the hammer is held off, so the
    hole becomes a lemma (stated by the model, hypothesis included), applied
    to the clause's variables and proved one level down.
    """

    target = write_target(
        project, "flipEq : (n m : Nat) → suc n ≡ m → m ≡ suc n\nflipEq n m eq = {!!}"
    )
    llm = ProofLLM(backend=EchoBackend(responses=[
        PROMOTE_SKETCH,
        "nonsense",                                   # the hole's term: wrong
        "(n m : Nat) → suc n ≡ m → suc n ≡ m",        # the lemma's statement
        LEMMA_SKETCH,
        "eq",                                         # the lemma's hole
    ]))

    result = prove_dsp(
        target,
        "flipEq",
        llm=llm,
        draft=False,
        sketch_max_attempts=1,
        hammer=HammerConfig(tactics=(), use_mimer=False, llm_attempts=1),
        history=ProofHistory(),
        verbose=False,
    )

    assert result.success, result.output
    lemma = [r for r in result.gap_results if r.method.startswith("lemma:")]
    assert lemma and lemma[0].solution == "flipEq-gap0 n m eq"
    assert result.lemma_results and result.lemma_results[0].success
