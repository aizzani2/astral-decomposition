module ListReversal where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

infixr 5 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

infixr 5 _++_
_++_ : ∀ {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

reverse : ∀ {A : Set} -> List A -> List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ (x :: [])

reverse-involutive : ∀ {A : Set} (xs : List A) -> reverse (reverse xs) ≡ xs
reverse-involutive xs = {!   !}