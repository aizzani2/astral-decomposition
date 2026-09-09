module Tests.Util where

open import Agda.Builtin.Nat public
open import Agda.Builtin.Equality public

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q
-- First-order congruence for `suc`. Mimer (Agda's auto) cannot synthesise
-- higher-order arguments such as `cong suc`, so without this it never finds
-- `trans (plusSucRight n m) (congSuc (addComm n m))` and settles for a
-- non-terminating recursive call instead. Library support for the hammer.
congSuc : {x y : Nat} → x ≡ y → suc x ≡ suc y
congSuc refl = refl
