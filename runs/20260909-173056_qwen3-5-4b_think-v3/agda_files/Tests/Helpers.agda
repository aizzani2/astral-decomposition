module Tests.Helpers where

open import Tests.Context

plusZeroRight : (n : Nat) → n + 0 ≡ n
-- Base case: when n is zero, 0 + 0 reduces to 0, so the two sides are equal.
plusZeroRight zero = refl
-- Inductive case: suppose n + 0 = n. Then (suc n) + 0 reduces to suc (n + 0), and rewriting with the induction hypothesis turns this into suc n.
plusZeroRight (suc n) = congSuc (plusZeroRight n)
