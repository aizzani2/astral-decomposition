"""Agda-backed checks on the toy tree, including the whole DSP pipeline with a scripted model."""

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
def test_holes_and_unsolved_metas(toy_tree: Path):
    f = write_target(toy_tree, "g : (n : Nat) → n + 0 ≡ n\ng n = {!!}")
    assert check_sketch(f, import_path=str(toy_tree), with_context=False).kind == "holes"

    f.write_text(f.read_text().replace("{!!}", "_"))
    result = check_sketch(f, import_path=str(toy_tree), with_context=False)
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
def test_decompose_and_export_step_sketch(toy_tree: Path):
    f = write_target(toy_tree, ADD_COMM)
    before = f.read_text()
    d = decompose(f, "addComm", str(toy_tree))

    assert [len(c.steps) for c in d.clauses] == [1, 2]
    assert d.clauses[1].steps[0].recursive

    sketch = export_sketch(f, "addComm", "step", str(toy_tree), decomposition=d)
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
def test_dsp_pipeline_end_to_end_with_scripted_model(toy_tree: Path):
    target = write_target(toy_tree, "plusZero : (n : Nat) → n + 0 ≡ n\nplusZero n = {!!}")
    llm = ProofLLM(backend=EchoBackend(responses=[DRAFT, SKETCH]))

    result = prove_dsp(
        agda_file=target,
        helpers_file=toy_tree / "Tests" / "Helpers.agda",
        helper_goal_file=toy_tree / "Tests" / "HelperGoal.agda",
        llm=llm,
        draft_samples=1,
        sketch_max_attempts=1,
        hammer=HammerConfig(llm_attempts=0, import_path=str(toy_tree)),
        history=ProofHistory(),
        verbose=False,
    )

    assert result.success, result.output
    assert result.stage == "done"
    assert {r.method.split(":")[0] for r in result.gap_results} <= {"tactic", "mimer"}
    assert "plusZero (suc n) = " in result.final_source


@needs_agda
def test_session_hammer_rejects_non_terminating_recursion(toy_tree: Path):
    from core.agda_client import AgdaSession
    from core.hammer import close_gap
    from util.sketch_ops import build_gaps

    f = write_target(toy_tree, "plusZero : (n : Nat) → n + 0 ≡ n\nplusZero zero = refl\nplusZero (suc n) = {!!}")
    source = f.read_text()
    check = check_sketch(f, import_path=str(toy_tree), with_context=True)
    gap = build_gaps(source, check.goals)[0]
    config = HammerConfig(
        tactics=("plusZero (suc n)", "congSuc (plusZero n)"), use_mimer=False,
        llm_attempts=0, import_path=str(toy_tree),
    )

    with AgdaSession(f, import_path=str(toy_tree)) as session:
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
def test_function_typed_hole_gets_binders_and_no_draft(toy_tree: Path):
    target = write_target(toy_tree, "symm : {x y : Nat} → x ≡ y → y ≡ x\nsymm = {!!}")
    llm = ProofLLM(backend=EchoBackend(responses=[POINT_FREE_SKETCH]))   # no draft call

    result = prove_dsp(
        agda_file=target,
        helpers_file=toy_tree / "Tests" / "Helpers.agda",
        helper_goal_file=toy_tree / "Tests" / "HelperGoal.agda",
        llm=llm,
        draft=False,
        sketch_max_attempts=1,
        hammer=HammerConfig(llm_attempts=0, import_path=str(toy_tree)),
        history=ProofHistory(),
        verbose=False,
    )

    assert result.success, result.output
    assert "λ" in result.final_source                    # the binder Agda introduced


@needs_agda
def test_formalizer_hole_promotion_and_recursion(toy_tree: Path):
    """
    The formalizer's proof has a wrong term; a hole goes there; with the
    hammer held off, the hole becomes a lemma over the clause's variables
    (its hypothesis included), which the formalizer then proves one level down.
    """

    from proof.formalizer import FormalizerLLM

    target = write_target(
        toy_tree, "flipEq : (n m : Nat) → suc n ≡ m → m ≡ suc n\nflipEq n m eq = {!!}"
    )
    formalizer = FormalizerLLM(
        drafter=ProofLLM(backend=EchoBackend(responses=[])),
        backend=EchoBackend(responses=[
            "flipEq zero m eq = sym eq\nflipEq (suc n) m eq = nonsense eq",   # theorem
            "flipEq-gap0 n m eq = sym eq",                                     # promoted lemma
        ]),
    )

    result = prove_dsp(
        agda_file=target,
        helpers_file=toy_tree / "Tests" / "Helpers.agda",
        helper_goal_file=toy_tree / "Tests" / "HelperGoal.agda",
        llm=formalizer,
        draft=False,
        sketch_max_attempts=1,
        hammer=HammerConfig(tactics=(), use_mimer=False, llm_attempts=0, import_path=str(toy_tree)),
        history=ProofHistory(),
        verbose=False,
        place_holes=True,
    )

    assert result.success, result.output
    lemma = [r for r in result.gap_results if r.method.startswith("lemma:")]
    assert lemma and "(eq : suc (suc n) ≡ m)" in lemma[0].method   # hypothesis kept
    assert result.lemma_results and result.lemma_results[0].success
