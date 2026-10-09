"""Text-level parsing: holes, declarations, clauses, chains, signatures. No Agda."""

from core.proof_context import find_enclosing_top_level_decl_name, get_signature_line
from util.agda_source import declaration_span, parse_chain, parse_clauses, split_equation
from util.sketch_ops import count_holes, mask_comments, replace_hole


def test_holes_are_standalone_question_marks_or_braces():
    assert count_holes("f = ?") == 1
    assert count_holes("f = (? )") == 1
    assert count_holes("m ≤? n") == 0          # part of a name
    assert count_holes("_≟_ ?x") == 0
    assert count_holes("{! x !} ?") == 2
    assert count_holes("-- why ?\nf = ?") == 1    # comments are not code


def test_literate_prose_is_not_code():
    src = "# Title?\nWhy ? because\n```agda\nf : Nat\nf = ?\n```\nmore ? prose\n"
    assert count_holes(src) == 1
    assert len(mask_comments(src)) == len(src)


def test_replace_hole_by_index():
    assert replace_hole("a = {!!}\nb = ?", 1, "refl") == "a = {!!}\nb = refl"


NESTED = """module M where
module _ {a} where
  foo : (n : Nat) →
        n ≡ n
  foo n = trans step {!!}
    where
    step : n ≡ n
    step = {!!}
  baz : Nat
  baz = q where q = {!!}
bar : Nat
bar = {!!}
"""


def test_target_of_a_hole_skips_where_locals_and_module_headers():
    assert [find_enclosing_top_level_decl_name(NESTED, n) for n in (5, 8, 10, 12)] == [
        "foo", "foo", "baz", "bar",
    ]


def test_signature_line_joins_continuations():
    assert get_signature_line(NESTED, "foo") == "foo : (n : Nat) → n ≡ n"


def test_declaration_span_nested():
    start, body, end, column = declaration_span(NESTED, "foo")
    assert column == 2
    assert NESTED[start:body].strip().startswith("foo : (n : Nat)")
    assert NESTED[body:end].strip().startswith("foo n = trans step")
    assert "baz" not in NESTED[body:end]


def test_clauses_with_implicit_patterns_rewrite_and_with():
    src = """f : (n : Nat) → Nat
f {n = zero} x = x
f (suc n) rewrite p n = q
f m with g m
... | yes p = p
... | no _ = zero
"""
    _, clauses = parse_clauses(src, "f")
    kinds = [(c.lhs.split()[1] if c.lhs.startswith("f") else c.lhs[:3], c.rhs, c.note) for c in clauses]
    assert kinds[0] == ("{n", "x", "")                       # `=` inside braces is not the clause's
    assert kinds[1][1] == "q"                                 # rewrite: rhs after the free `=`
    assert kinds[2][2] == "with header"
    assert [c.rhs for c in clauses[3:]] == ["p", "zero"]      # with continuations are clauses


def test_chain_forms():
    text = """begin-equality
  a ≡⟨⟩
  b ≡⟨ cong suc (f x) ⟩
  c ≡˘⟨ g ⟩
  d ≡⟨ h ⟨
  e ∎"""
    steps = parse_chain(text, 0)
    assert [(s.lhs, s.rhs, s.justification, s.reversed) for s in steps] == [
        ("a", "b", "", False),
        ("b", "c", "cong suc (f x)", False),
        ("c", "d", "g", True),
        ("d", "e", "h", True),
    ]
    assert text[steps[1].span[0]:steps[1].span[1]] == "cong suc (f x)"


def test_not_a_chain():
    assert parse_chain("trans p q", 0) is None
    assert parse_chain("λ x → begin a ≡⟨ p ⟩ b ∎", 0) is None


def test_split_equation_at_top_level():
    assert split_equation("f (a ≡ b) ≡ c") == ("f (a ≡ b)", "c")
