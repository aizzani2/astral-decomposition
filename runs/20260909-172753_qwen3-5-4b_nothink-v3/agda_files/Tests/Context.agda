module Tests.Context where

open import Tests.Util public

data Divides (d n : Nat) : Set where
  divides : (k : Nat) → n ≡ d * k → Divides d n

data DividesDiff (d a b : Nat) : Set where
  dividesDiff : (k : Nat) → a ≡ b + d * k → DividesDiff d a b

pow : Nat → Nat → Nat
pow zero n = 1
pow (suc e) n = n * pow e n