module Tests.Helpers where

open import Tests.Context

plusZeroRight : (n : Nat) → n + 0 ≡ n
-- Base case: when n is zero, the expression 0 + 0 reduces to 0, which equals the right-hand side.
plusZeroRight zero = refl
-- Inductive hypothesis: assume that for an arbitrary natural number m, we have m + 0 = m.
-- Inductive case: consider suc n. The left-hand side is (suc n) + 0, which reduces to suc (n + 0). By the inductive hypothesis, this equals suc n, matching the right-hand side.
plusZeroRight (suc n) = congSuc (plusZeroRight n)

addComm-gap1 : (m n : Nat) → suc m + n ≡ m + (suc n)
-- Inductive case: structural induction on the first argument.
addComm-gap1 zero n = refl
-- Inductive case: assume hypothesis and reduce both sides.
addComm-gap1 (suc m) n = congSuc (addComm-gap1 m n)
