{-# OPTIONS --without-K #-}

module SigmaIdentity where

open import Agda.Primitive using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

transport : ∀ {a b} {A : Set a} (B : A → Set b) {x y : A} → x ≡ y → B x → B y
transport B refl bx = bx

record _≃_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

Σ-≡-≃ : ∀ {a b} {A : Set a} {B : A → Set b} (s t : Σ A B)
      → (s ≡ t) ≃ Σ (fst s ≡ fst t) (λ p → transport B p (snd s) ≡ snd t)
Σ-≡-≃ s t = ?