-- What the test theorems may use: naturals, equality, and the lemmas a
-- hammer needs to close equational holes.
module Base where

open import Agda.Builtin.Nat public
open import Agda.Builtin.Equality public

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

-- First-order congruence for `suc`: Mimer cannot synthesise `cong suc`.
congSuc : {x y : Nat} → x ≡ y → suc x ≡ suc y
congSuc refl = refl
