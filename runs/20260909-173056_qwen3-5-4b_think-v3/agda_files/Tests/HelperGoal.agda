module Tests.HelperGoal where

open import Tests.Context
open import Tests.Helpers

-- We also need that m + suc n = suc (m + n) for all m and n; again, we record this property via an independent proof step which acts as a lemma.
plusSucLeft : (m n : Nat) → m + suc n ≡ suc (m + n)
plusSucLeft = {!!}
