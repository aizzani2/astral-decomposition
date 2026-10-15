"""Agda-backed checks on the fixture project, including the whole DSP pipeline with a scripted model."""

from pathlib import Path

from core.agda_client import check_sketch
from core.hammer import HammerConfig
from core.llm_client import EchoBackend, ProofLLM
from core.proof_history import ProofHistory
from proof.proof_sketch import prove_dsp
from tests.conftest import needs_agda, write_target
from deproof.decompose import decompose
from deproof.sketch_export import export_sketch


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
    from core.sketch_ops import build_gaps

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


@needs_agda
def test_definition_format_holes_and_stated_lemma(project: Path):
    """
    A signature -> definition model's proof has a wrong term; a hole goes
    there; with the hammer held off, the hole becomes a lemma stating its goal
    over the clause's variables (hypothesis included), which the model then
    proves one level down from the lemma's signature.
    """

    target = write_target(
        project, "flipEq : (n m : Nat) → suc n ≡ m → m ≡ suc n\nflipEq n m eq = {!!}"
    )
    llm = ProofLLM(sketch_format="definition", backend=EchoBackend(responses=[
        "  flipEq zero m eq = sym eq\n  flipEq (suc n) m eq = nonsense eq",   # theorem, indented
        "flipEq-gap0 n m eq = sym eq",                                     # stated lemma
    ]))

    result = prove_dsp(
        target,
        "flipEq",
        llm=llm,
        draft=False,
        sketch_max_attempts=1,
        hammer=HammerConfig(tactics=(), use_mimer=False, llm_attempts=0),
        history=ProofHistory(),
        verbose=False,
        place_holes=True,
        state_lemmas=True,
    )

    assert result.success, result.output
    lemma = [r for r in result.gap_results if r.method.startswith("lemma:")]
    assert lemma and "(eq : suc (suc n) ≡ m)" in lemma[0].method   # hypothesis kept
    assert llm.backend.calls[0].startswith("<signature>flipEq : (n m : Nat)")
    assert result.lemma_results and result.lemma_results[0].success


@needs_agda
def test_continuation_format_sees_the_file_and_continues(project: Path):
    """A raw-Agda model gets the file up to the signature and writes the clauses."""

    target = write_target(project, "flipEq : (n m : Nat) → suc n ≡ m → m ≡ suc n\nflipEq n m eq = {!!}")
    llm = ProofLLM(sketch_format="continuation", backend=EchoBackend(responses=["flipEq n m eq = sym eq\n"]))

    result = prove_dsp(
        target, "flipEq", llm=llm, draft=False, sketch_max_attempts=1,
        hammer=HammerConfig(tactics=(), use_mimer=False, llm_attempts=0),
        history=ProofHistory(), verbose=False, place_holes=True,
    )

    prompt = llm.backend.calls[0]
    assert "open import Base" in prompt
    assert prompt.endswith("flipEq : (n m : Nat) → suc n ≡ m → m ≡ suc n\n")
    assert result.success, result.output


@needs_agda
def test_proof_hiding_a_postulate_is_rejected(project: Path):
    """The fixture has no --safe, so Agda accepts this; the final check must not."""

    target = write_target(project, "flipEq : (n m : Nat) → suc n ≡ m → m ≡ suc n\nflipEq n m eq = {!!}")
    llm = ProofLLM(sketch_format="definition", backend=EchoBackend(responses=[
        "flipEq n m eq = cheat\n  where\n  postulate cheat : m ≡ suc n\n",
    ]))

    result = prove_dsp(
        target, "flipEq", llm=llm, draft=False, sketch_max_attempts=1,
        hammer=HammerConfig(tactics=(), use_mimer=False, llm_attempts=0),
        history=ProofHistory(), verbose=False, place_holes=True, state_lemmas=True,
    )

    assert not result.success
    assert result.stage == "final_check" and "postulate" in result.output


@needs_agda
def test_planner_states_lemmas_and_the_prover_uses_them(project: Path):
    """
    A chat planner states a lemma; the continuation prover sees it postulated
    just above the theorem, uses it, and then proves it one level down.
    """

    target = write_target(project, "flipEq : (n m : Nat) → suc n ≡ m → m ≡ suc n\nflipEq n m eq = {!!}")
    planner = ProofLLM(backend=EchoBackend(responses=[
        "symNat : (a b : Nat) → a ≡ b → b ≡ a\n</AGDA_LEMMAS>\n<AGDA_SKETCH>\n"
        "flipEq : (n m : Nat) → suc n ≡ m → m ≡ suc n\nflipEq n m eq = {!!}\n",     # the theorem's plan
        "</AGDA_LEMMAS>\n<AGDA_SKETCH>\nsymNat : (a b : Nat) → a ≡ b → b ≡ a\nsymNat a b p = {!!}\n",
    ]))
    prover = ProofLLM(sketch_format="continuation", planner=planner, backend=EchoBackend(responses=[
        "flipEq n m eq = symNat (suc n) m eq\n",     # uses the planner's lemma
        "symNat a b p = sym p\n",                    # proves it
    ]))

    result = prove_dsp(
        target, "flipEq", llm=prover, draft=False, sketch_max_attempts=1,
        hammer=HammerConfig(tactics=(), use_mimer=False, llm_attempts=0),
        history=ProofHistory(), verbose=False, place_holes=True, state_lemmas=True,
    )

    assert "postulate\n  symNat : (a b : Nat) → a ≡ b → b ≡ a" in prover.backend.calls[0]
    assert result.success, result.output
    assert [r.target_name for r in result.lemma_results] == ["symNat"]
    assert result.lemma_results[0].success


CHAIN = """
plusZero : (n : Nat) → n + 0 ≡ n
plusZero zero = refl
plusZero (suc n) = congSuc (plusZero n)

plusZeroTwice : (n : Nat) → (n + 0) + 0 ≡ n
plusZeroTwice n = trans (plusZero (n + 0)) (plusZero n)

thm : (n : Nat) → ((n + 0) + 0) + 0 ≡ n
thm n = trans (plusZero ((n + 0) + 0)) (plusZeroTwice n)
"""


@needs_agda
def test_lemma_tree_and_hiding_a_level(project: Path):
    from deproof.tree import lemma_tree
    from proof.layout import Layout

    f = write_target(project, CHAIN)
    nodes = lemma_tree(f, "thm", max_depth=2)

    assert {n: v.depth for n, v in nodes.items()} == {"thm": 0, "plusZero": 1, "plusZeroTwice": 1}
    assert nodes["plusZeroTwice"].children == ["plusZero"]

    # hide the direct lemmas: what is left loads, with the theorem as a hole
    source = f.read_text()
    lines = source.splitlines()
    first = lines.index("plusZero : (n : Nat) → n + 0 ≡ n") + 1
    last = lines.index("plusZeroTwice n = trans (plusZero (n + 0)) (plusZero n)") + 1
    Layout(f, "thm", None, [(first, last)])
    assert "plusZero" not in f.read_text().split("thm :")[0]
    assert check_sketch(f, with_context=False).kind == "holes"
