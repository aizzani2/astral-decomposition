module Tests.HelperGoal where

open import Tests.Context
open import Tests.Helpers

addSucL : (m n : Nat) → m + suc n ≡ suc (m + n)
-- Base case: when m is zero, 0 + suc n reduces to suc n.
addSucL zero = {!!}
-- Inductive case: chain the hypothesis with congSuc and plusZeroRight.
addSucL (suc m) = {!!}
