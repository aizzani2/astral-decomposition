module Tests.HelperGoal where

open import Tests.Context
open import Tests.Helpers

-- Inductive case: pattern match on the second argument and use plusZeroRight if needed, though standard proofs usually induct on one variable directly here based on the sketch structure requiring two holes for full generality or specific reduction steps implied by "hard" lemma needs in informal text. However, following strict structural induction style often used with commutativity where we might need to reduce both sides: Actually, looking at standard proofs and the requirement to leave hard parts as holes based on the informal proof's two main lemmas + cases structure which implies we are building a skeleton for addComm that relies on plusZeroRight.
addComm-gap1 : (m n : Nat) → suc m + n ≡ m + (suc n)
addComm-gap1 = {!!}
