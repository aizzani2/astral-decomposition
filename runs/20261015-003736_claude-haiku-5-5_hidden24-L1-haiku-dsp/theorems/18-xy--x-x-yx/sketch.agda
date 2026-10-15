------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Algebra.Bundles using (KleeneAlgebra)

module Algebra.Properties.KleeneAlgebra {k₁ k₂} (K : KleeneAlgebra k₁ k₂) where

open KleeneAlgebra K
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid

0⋆≈1 : 0# ⋆ ≈ 1#
0⋆≈1 = begin
  0# ⋆           ≈⟨ sym (starExpansiveˡ 0#) ⟩
  1# + 0# ⋆ * 0# ≈⟨ +-congˡ ( zeroʳ (0# ⋆)) ⟩
  1# + 0#        ≈⟨ +-identityʳ 1# ⟩
  1#             ∎

1+x⋆≈x⋆ : ∀ x → 1# + x ⋆ ≈ x ⋆
1+x⋆≈x⋆ x = sym (begin
  x ⋆                   ≈⟨ sym (starExpansiveʳ x) ⟩
  1# + x * x ⋆          ≈⟨ +-congʳ (sym (+-idem 1#)) ⟩
  1# + 1# + x * x ⋆     ≈⟨ +-assoc 1# 1# ((x * x ⋆ )) ⟩
  1# + (1# + x * x ⋆)   ≈⟨ +-congˡ (starExpansiveʳ x) ⟩
  1# + x ⋆              ∎)

x⋆+xx⋆≈x⋆ : ∀ x → x ⋆ + x * x ⋆ ≈ x ⋆
x⋆+xx⋆≈x⋆ x = begin
  x ⋆ + x * x ⋆         ≈⟨ +-congʳ (sym (1+x⋆≈x⋆ x)) ⟩
  1# + x ⋆ + x * x ⋆    ≈⟨ +-congʳ (+-comm 1# ((x ⋆))) ⟩
  x ⋆ + 1# + x * x ⋆    ≈⟨ +-assoc ((x ⋆)) 1# ((x * x ⋆ )) ⟩
  x ⋆ + (1# + x * x ⋆)  ≈⟨ +-congˡ (starExpansiveʳ x) ⟩
  x ⋆ + x ⋆             ≈⟨ +-idem (x ⋆) ⟩
  x ⋆                   ∎

x⋆+x⋆x≈x⋆ : ∀ x → x ⋆ + x ⋆ * x ≈ x ⋆
x⋆+x⋆x≈x⋆ x = begin
  x ⋆ + x ⋆ * x         ≈⟨ +-congʳ (sym (1+x⋆≈x⋆ x)) ⟩
  1# + x ⋆ + x ⋆ * x    ≈⟨ +-congʳ (+-comm 1# (x ⋆)) ⟩
  x ⋆ + 1# + x ⋆ * x    ≈⟨ +-assoc (x ⋆) 1# (x ⋆ * x) ⟩
  x ⋆ + (1# + x ⋆ * x)  ≈⟨ +-congˡ (starExpansiveˡ x) ⟩
  x ⋆ + x ⋆             ≈⟨ +-idem (x ⋆) ⟩
  x ⋆                   ∎

x+x⋆≈x⋆ : ∀ x → x + x ⋆ ≈ x ⋆
x+x⋆≈x⋆ x = begin
  x + x ⋆                  ≈⟨ +-congˡ (sym (starExpansiveʳ x)) ⟩
  x + (1# + x * x ⋆)       ≈⟨ +-congʳ (sym (*-identityʳ x)) ⟩
  x * 1# + (1# + x * x ⋆)  ≈⟨ sym (+-assoc (x * 1#) 1# (x * x ⋆)) ⟩
  x * 1# + 1# + x * x ⋆    ≈⟨ +-congʳ (+-comm (x * 1#) 1#) ⟩
  1# + x * 1# + x * x ⋆    ≈⟨ +-assoc 1# (x * 1#) (x * x ⋆) ⟩
  1# + (x * 1# + x * x ⋆)  ≈⟨ +-congˡ (sym (distribˡ x 1# ((x ⋆)))) ⟩
  1# + x * (1# + x ⋆)      ≈⟨ +-congˡ (*-congˡ (1+x⋆≈x⋆ x)) ⟩
  1# + x * x ⋆             ≈⟨ (starExpansiveʳ x) ⟩
  x ⋆                      ∎

1+x+x⋆≈x⋆ : ∀ x → 1# + x + x ⋆ ≈ x ⋆
1+x+x⋆≈x⋆ x = begin
  1# + x + x ⋆    ≈⟨ +-assoc 1# x (x ⋆) ⟩
  1# + (x + x ⋆)  ≈⟨ +-congˡ (x+x⋆≈x⋆ x) ⟩
  1# + x ⋆        ≈⟨ 1+x⋆≈x⋆ x ⟩
  x ⋆             ∎

0+x+x⋆≈x⋆ : ∀ x → 0# + x + x ⋆ ≈ x ⋆
0+x+x⋆≈x⋆ x = begin
  0# + x + x ⋆    ≈⟨ +-assoc 0# x (x ⋆) ⟩
  0# + (x + x ⋆)  ≈⟨ +-identityˡ ((x + x ⋆)) ⟩
  (x + x ⋆)       ≈⟨ x+x⋆≈x⋆ x ⟩
  x ⋆             ∎

x⋆x⋆≈x⋆ : ∀ x → x ⋆ * x ⋆ ≈ x ⋆
x⋆x⋆≈x⋆ x = starDestructiveˡ x (x ⋆) (x ⋆) (x⋆+xx⋆≈x⋆ x)

1+x⋆x⋆≈x⋆ : ∀ x → 1# + x ⋆ * x ⋆ ≈ x ⋆
1+x⋆x⋆≈x⋆ x = begin
  1# + x ⋆ * x ⋆  ≈⟨ +-congˡ (x⋆x⋆≈x⋆ x) ⟩
  1# + x ⋆        ≈⟨ 1+x⋆≈x⋆ x ⟩
  x ⋆             ∎

x⋆⋆≈x⋆ : ∀ x → (x ⋆) ⋆ ≈ x ⋆
x⋆⋆≈x⋆ x = begin
  (x ⋆) ⋆        ≈⟨ sym (*-identityʳ ((x ⋆) ⋆)) ⟩
  (x ⋆) ⋆ * 1#   ≈⟨ starDestructiveˡ (x ⋆) 1# (x ⋆) (1+x⋆x⋆≈x⋆ x) ⟩
  x ⋆            ∎

1+11≈1 : 1# + 1# * 1# ≈ 1#
1+11≈1 = begin
  1# + 1# * 1#  ≈⟨ +-congˡ ( *-identityʳ 1#) ⟩
  1# + 1#       ≈⟨ +-idem 1# ⟩
  1#            ∎

1⋆≈1 : 1# ⋆ ≈ 1#
1⋆≈1 = begin
  1# ⋆       ≈⟨ sym (*-identityʳ (1# ⋆)) ⟩
  1# ⋆ * 1#  ≈⟨ starDestructiveˡ 1# 1# 1# 1+11≈1 ⟩
  1#         ∎

x≈y⇒1+xy⋆≈y⋆ : ∀ x y → x ≈  y → 1# + x * y ⋆ ≈ y ⋆
x≈y⇒1+xy⋆≈y⋆ x y eq = begin
  1# + x * y ⋆  ≈⟨ +-congˡ (*-congʳ (eq)) ⟩
  1# + y * y ⋆  ≈⟨ starExpansiveʳ y ⟩
  y ⋆           ∎

x≈y⇒x⋆≈y⋆ : ∀ x y → x ≈ y → x ⋆ ≈ y ⋆
x≈y⇒x⋆≈y⋆ x y eq = begin
  x ⋆       ≈⟨ sym (*-identityʳ (x ⋆)) ⟩
  x ⋆ * 1#  ≈⟨ (starDestructiveˡ x 1# (y ⋆) (x≈y⇒1+xy⋆≈y⋆ x y eq)) ⟩
  y ⋆       ∎

ax≈xb⇒x+axb⋆≈xb⋆ : ∀ x a b → a * x ≈ x * b → x + a * (x * b ⋆) ≈ x * b ⋆
ax≈xb⇒x+axb⋆≈xb⋆ x a b eq = begin
  x + a * (x * b ⋆)       ≈⟨ +-congˡ (sym(*-assoc a x (b ⋆))) ⟩
  x + a * x * b ⋆         ≈⟨ +-congʳ (sym (*-identityʳ x)) ⟩
  x * 1# + a * x * b ⋆    ≈⟨ +-congˡ (*-congʳ (eq)) ⟩
  x * 1# + x * b * b ⋆    ≈⟨ +-congˡ (*-assoc x b (b ⋆) ) ⟩
  x * 1# + x * (b * b ⋆)  ≈⟨ sym (distribˡ x 1# (b * b ⋆)) ⟩
  x * (1# + b * b ⋆)      ≈⟨ *-congˡ (starExpansiveʳ b) ⟩
  x * b ⋆                 ∎

-- dsp: lemmas
postulate
  leq-plus-right : ∀ b c → b + (b + c) ≈ b + c

postulate
  leq-antisym : ∀ a b → a + b ≈ b → b + a ≈ a → a ≈ b

postulate
  leq-trans : ∀ a b c → a + b ≈ b → b + c ≈ c → a + c ≈ c

postulate
  mono-left : ∀ r p q → p + q ≈ q → r * p + r * q ≈ r * q

postulate
  mono-right : ∀ r p q → p + q ≈ q → p * r + q * r ≈ q * r

postulate
  star-le-right : ∀ a → a * a ⋆ + a ⋆ ≈ a ⋆

postulate
  star-le-left : ∀ a → a ⋆ * a + a ⋆ ≈ a ⋆

postulate
  one-le-star : ∀ a → 1# + a ⋆ ≈ a ⋆

postulate
  left-induction : ∀ a b c → (b + a * c) + c ≈ c → (a ⋆ * b) + c ≈ c

postulate
  right-induction : ∀ a b c → (b + c * a) + c ≈ c → (b * a ⋆) + c ≈ c

-- dsp: end of lemmas
[xy]⋆x≈x[yx]⋆ : ∀ x y → (x * y) ⋆ * x ≈ x * (y * x) ⋆
-- Step 7: prove both inequalities separately, then conclude by antisymmetry (step 18).
[xy]⋆x≈x[yx]⋆ x y = leq-antisym ((x * y) ⋆ * x) (x * (y * x) ⋆)
  -- Step 12: left induction with b = x, a = x·y, c = z = x·(y·x)*.
  -- The hypothesis x + (x·y)·z ≤ z comes from steps 8–11.
  (left-induction (x * y) x (x * (y * x) ⋆)
    -- Step 8: rewrite (x·y)·z as x·((y·x)·(y·x)*) by associativity.
    -- Step 9: (y·x)·(y·x)* ≤ (y·x)*, so by monotone x·((y·x)·(y·x)*) ≤ z.
    -- Step 10: 1 ≤ (y·x)*, so x = x·1 ≤ z by monotone.
    -- Step 11: combine steps 9 and 10 using idempotence of +.
    {!!})
  -- Step 17: right induction with b = x, a = y·x, c = w = (x·y)*·x.
  -- The hypothesis x + w·(y·x) ≤ w comes from steps 13–16.
  (right-induction (y * x) x ((x * y) ⋆ * x)
    -- Step 13: rewrite w·(y·x) as ((x·y)*·(x·y))·x by associativity.
    -- Step 14: (x·y)*·(x·y) ≤ (x·y)*, so by monotone ((x·y)*·(x·y))·x ≤ w.
    -- Step 15: 1 ≤ (x·y)*, so x = 1·x ≤ w by monotone.
    -- Step 16: combine steps 14 and 15 using idempotence of +.
    {!!})
