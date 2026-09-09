module Tests.Target where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

open import Tests.Util
open import Tests.Helpers
open import Tests.Context

addComm : (n m : Nat) → n + m ≡ m + n
-- Base case: when first argument is zero, 0 + m reduces to m and we apply plusZeroRight.
addComm zero m = sym (plusZeroRight m)
-- Inductive step: assume addComm holds for smaller n; use IH with suc (n).
addComm (suc n) m = trans (congSuc (addComm n m)) (sym (plusSucLeft m n))
