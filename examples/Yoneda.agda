{-# OPTIONS --without-K #-}

module Yoneda where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- funext is not in normal Agda
postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
         → (∀ x → f x ≡ g x) → f ≡ g

record _≃_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

record Category (o h : Level) : Set (lsuc (o ⊔ h)) where
  field
    Ob    : Set o
    Hom   : Ob → Ob → Set h
    id    : ∀ {x} → Hom x x
    _∘_   : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    idˡ   : ∀ {x y} (f : Hom x y) → (id ∘ f) ≡ f
    idʳ   : ∀ {x y} (f : Hom x y) → (f ∘ id) ≡ f
    assoc : ∀ {w x y z} (f : Hom y z) (g : Hom x y) (k : Hom w x)
          → ((f ∘ g) ∘ k) ≡ (f ∘ (g ∘ k))

-- a presheaf on C, valued in Set ℓ (contravariant action P₁).
record Presheaf {o h} (C : Category o h) (ℓ : Level)
  : Set (o ⊔ h ⊔ lsuc ℓ) where
  open Category C
  field
    P₀   : Ob → Set ℓ
    P₁   : ∀ {x y} → Hom x y → P₀ y → P₀ x
    P-id : ∀ {x} (p : P₀ x) → P₁ id p ≡ p
    P-∘  : ∀ {x y z} (f : Hom y z) (g : Hom x y) (p : P₀ z)
         → P₁ g (P₁ f p) ≡ P₁ (f ∘ g) p

-- natural transformations  Hom(-, c) ⇒ P
record YoNat {o h ℓ} {C : Category o h}
             (c : Category.Ob C) (P : Presheaf C ℓ)
  : Set (o ⊔ h ⊔ ℓ) where
  open Category C
  field
    η   : ∀ x → Hom x c → Presheaf.P₀ P x
    nat : ∀ {x y} (g : Hom x y) (k : Hom y c)
        → η x (k ∘ g) ≡ Presheaf.P₁ P g (η y k)

yoneda : ∀ {o h ℓ} {C : Category o h}
           (c : Category.Ob C) (P : Presheaf C ℓ)
       → YoNat c P ≃ Presheaf.P₀ P c
yoneda c P = {!   !}
