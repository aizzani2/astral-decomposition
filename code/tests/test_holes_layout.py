"""Hole placement helpers, model output parsing, the lemma layout, comparison. No Agda."""

from pathlib import Path

from core.proof_state import ProofObligation
from proof.holes import (
    _enclosing_spans,
    _error_span,
    _error_text,
    hole_chain_justifications,
    sketch_clauses,
    split_declaration,
)
from proof.layout import REGION_END, REGION_START, Layout
from util.deproof import ClauseDecomposition, Decomposition, ProofStep, compare


def test_chain_justifications_become_holes():
    clauses = "f = begin\n  a ≈⟨ p ⟩\n  b ≈⟨⟩\n  c ≡˘⟨ q x ⟩\n  d ≡⟨ r ⟨\n  e ∎"
    assert hole_chain_justifications(clauses) == (
        "f = begin\n  a ≈⟨ {!!} ⟩\n  b ≈⟨⟩\n  c ≡˘⟨ {!!} ⟩\n  d ≡⟨ {!!} ⟨\n  e ∎"
    )


def test_error_span_and_text():
    trial = "x\nf a = g a , h\n"
    span = _error_span("F.agda:2.7-10: error: [NotInScope] g a", trial)
    assert trial[span[0]:span[1]] == "g a"
    assert _error_text("F.agda:2.7-10: error: X at F.agda:2.7-10") == ": error: X at"


def test_enclosing_spans_smallest_first():
    trial = "d x = R.f x y , (begin a ∎)\n"
    rhs = (trial.index("R.f"), len(trial.rstrip()))
    error = (trial.index("R.f"), trial.index("R.f") + 3)
    spans = [trial[a:b] for a, b in _enclosing_spans(trial, error, rhs)]
    assert spans == ["R.f x y", "R.f x y , (begin a ∎)"]


def test_sketch_clauses_drops_signature_and_foreign_blocks():
    text = """f : Nat →
    Nat
-- base
f zero = zero
f (suc n) = n
helper : Nat
helper = zero
"""
    assert sketch_clauses(text, "f") == "-- base\nf zero = zero\nf (suc n) = n"


def test_split_declaration_multiline_signature():
    sig, clauses = split_declaration("lem : (n : Nat) →\n  n ≡ n\nlem n = refl", "lem")
    assert sig == "(n : Nat) → n ≡ n"
    assert clauses == "lem n = refl"


def test_layout_composes_and_blames(tmp_path: Path):
    f = tmp_path / "M.agda"
    f.write_text("{-# OPTIONS --safe #-}\nmodule M where\n  thm : Nat\n  thm = zero\n  after : Nat\n  after = thm\n")
    layout = Layout(f, "thm")
    text = f.read_text()

    assert "--safe" not in text                      # postulates must be allowed
    assert "after" not in text                       # cut after the theorem
    assert text.rstrip().endswith("thm = {!!}")

    lemmas = [ProofObligation("l1", "Nat"), ProofObligation("l2", "Bad")]
    layout.postulate(lemmas, before="thm")
    rendered = layout.render(text)
    lines = rendered.splitlines()
    assert lines.index(f"  {REGION_START}") < lines.index("    l2 : Bad") < lines.index(f"  {REGION_END}")

    row = lines.index("    l2 : Bad") + 1
    message = f"x.agda:{row - 10}.1-2: error: other\nx.agda:{row}.5-7: error: [NotInScope] Bad"
    assert layout.lemma_at_error(message, lemmas) == "l2"   # any of the reported positions

    layout.add_proved("l1 : Nat\nl1 = zero")
    assert layout.has_postulates()
    layout.restore([])
    assert not layout.has_postulates()


def _decomposition(name, clauses, lemmas, normal=None):
    return Decomposition(
        name=name, signature=f"{name} : T",
        clauses=[ClauseDecomposition(lhs=lhs, variables=vs, steps=[ProofStep(s, "j", "h") for s in steps])
                 for lhs, vs, steps in clauses],
        lemmas=lemmas, lemma_normal=normal or lemmas,
    )


def test_compare_split_up_to_variable_names():
    a = _decomposition("f", [("f zero m", ["m"], []), ("f (suc n) m", ["n", "m"], [])], {})
    b = _decomposition("f", [("f zero k", ["k"], []), ("f (suc j) k", ["j", "k"], [])], {})
    assert compare(a, b).same_split


def test_compare_lemmas_up_to_symmetry():
    a = _decomposition("f", [], {"mine": "(x y : N) → x + y ≡ y"})
    b = _decomposition("f", [], {"theirs": "(a b : N) → b ≡ a + b"})
    assert compare(a, b).lemma_pairs == [("mine", "theirs", "symmetric")]


def test_degenerate_promotion_sees_through_implicit_binders():
    from proof.proof_sketch import _is_degenerate

    goal = "trans f (refl id) ≈ᵗ f"
    assert _is_degenerate("{X : List Obj} → {f : Sublist X Y} → trans f (refl id) ≈ᵗ f", goal)
    assert _is_degenerate("(n : Nat) → {m : Nat} → trans f (refl id) ≈ᵗ f", goal)
    assert not _is_degenerate("(n : Nat) → n ≡ n", goal)
