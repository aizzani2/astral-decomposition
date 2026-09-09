module Tests.Helpers where

open import Tests.Context

plusZeroRight : (n : Nat) → n + 0 ≡ n
-- Base case: when n is zero, 0 + 0 reduces to 0, so the two sides are equal.
plusZeroRight zero = refl
-- Inductive step: assume n + 0 = n. Then (suc n) + 0 reduces to suc (n + 0), and rewriting with the induction hypothesis turns this into suc n.
plusZeroRight (suc n) = congSuc (plusZeroRight n)

plusSucLeft : (m n : Nat) → m + suc n ≡ suc (m + n)
-- Base case: 0 + suc n reduces to suc n, and suc (0 + n) also reduces to suc n.
plusSucLeft zero n = refl
-- Inductive case: assume m + suc n = suc (m + n). Then (suc m) + suc n reduces to suc (m + suc n), which by the induction hypothesis equals suc (suc (m + n)), which is suc ((suc m) + n).
plusSucLeft (suc m) n = congSuc (plusSucLeft m n)
