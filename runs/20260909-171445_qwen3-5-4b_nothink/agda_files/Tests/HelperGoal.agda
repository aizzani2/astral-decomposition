module Tests.HelperGoal where

open import Tests.Context
open import Tests.Helpers

-- Inductive case: Assume n + m = m + n. We need to show that (suc n) + m = m + (suc n). By definition, (suc n) + m = suc (n + m). Using the induction hypothesis, we have suc (n + m) = suc (m + n), and by definition again, suc (m + n) = m + (suc n). Therefore, (suc n) + m = m + (suc n).
addComm-gap1 : ∀ n m → suc n + m ≡ m + suc n
addComm-gap1 = {!!}
