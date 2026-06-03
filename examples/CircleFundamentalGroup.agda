{-# OPTIONS --without-K #-}

module CircleFundamentalGroup where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Integer using (ℤ)

-- paths but not too much
transport : ∀ {a b} {A : Set a} (P : A → Set b) {x y : A} → x ≡ y → P x → P y
transport P refl px = px

apd : ∀ {a b} {A : Set a} {P : A → Set b} (f : (x : A) → P x) {x y : A}
      (p : x ≡ y) → transport P p (f x) ≡ f y
apd f refl = refl

record _≃_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

postulate
  S¹       : Set
  base     : S¹
  loop     : base ≡ base
  S¹-elim  : ∀ {ℓ} (P : S¹ → Set ℓ) (b : P base)
             (ℓ' : transport P loop b ≡ b) → (x : S¹) → P x
  S¹-βbase : ∀ {ℓ} (P : S¹ → Set ℓ) (b : P base)
             (ℓ' : transport P loop b ≡ b) → S¹-elim P b ℓ' base ≡ b

ΩS¹≃ℤ : (base ≡ base) ≃ ℤ
ΩS¹≃ℤ = ?