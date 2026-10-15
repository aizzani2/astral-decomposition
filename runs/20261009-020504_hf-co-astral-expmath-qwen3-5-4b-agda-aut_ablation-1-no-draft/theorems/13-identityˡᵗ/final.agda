{-# OPTIONS --without-K #-}

-- A generalised form of Thinnings, as described in Conor Mc Bride's Everybody's Got To Be Somewhere
-- The traditional definition can be recovered by setting C to a discrete category

open import Categories.Category

module Categories.Category.Construction.Thinnings {o ℓ e} (C : Category o ℓ e) where

open import Categories.Object.Initial
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Binary.Sublist.Heterogeneous
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
open import Function.Base using (flip)
open import Level

open Category C

data _≈ᵗ_ : ∀ {X Y : List Obj} → Sublist _⇒_ X Y → Sublist _⇒_ X Y → Set (o ⊔ ℓ ⊔ e) where
  [] : [] ≈ᵗ []
  _∷ʳ_ : ∀ {xs ys} {fs gs : Sublist _⇒_ xs ys} y → fs ≈ᵗ gs → (y ∷ʳ fs) ≈ᵗ (y ∷ʳ gs)
  _∷_ : ∀ {x xs y ys} {f g : x ⇒ y} {fs gs : Sublist _⇒_ xs ys} → f ≈ g → fs ≈ᵗ gs → (f ∷ fs) ≈ᵗ (g ∷ gs)

private
  ≈ᵗ-refl : ∀ {X Y} {fs : Sublist _⇒_ X Y} → fs ≈ᵗ fs
  ≈ᵗ-refl {fs = []} = []
  ≈ᵗ-refl {fs = y ∷ʳ fs} = y ∷ʳ ≈ᵗ-refl
  ≈ᵗ-refl {fs = _ ∷ fs} = Equiv.refl ∷ ≈ᵗ-refl

  ≈ᵗ-sym : ∀ {X Y} {fs gs : Sublist _⇒_ X Y} → fs ≈ᵗ gs → gs ≈ᵗ fs
  ≈ᵗ-sym [] = []
  ≈ᵗ-sym (y ∷ʳ fs≈gs) = y ∷ʳ ≈ᵗ-sym fs≈gs
  ≈ᵗ-sym (f≈g ∷ fs≈gs) = Equiv.sym f≈g ∷ ≈ᵗ-sym fs≈gs

  ≈ᵗ-trans : ∀ {X Y} {fs gs hs : Sublist _⇒_ X Y} → fs ≈ᵗ gs → gs ≈ᵗ hs → fs ≈ᵗ hs
  ≈ᵗ-trans [] [] = []
  ≈ᵗ-trans (y ∷ʳ fs≈gs) (.y ∷ʳ gs≈hs) = y ∷ʳ ≈ᵗ-trans fs≈gs gs≈hs
  ≈ᵗ-trans (f≈g ∷ fs≈gs) (g≈h ∷ gs≈hs) = Equiv.trans f≈g g≈h ∷ ≈ᵗ-trans fs≈gs gs≈hs

  assocᵗ : ∀ {W X Y Z : List Obj} {f : Sublist _⇒_ W X} {g : Sublist _⇒_ X Y} {h : Sublist _⇒_ Y Z}
         → trans (flip _∘_) f (trans (flip _∘_) g h) ≈ᵗ trans (flip _∘_) (trans (flip _∘_) f g) h
  assocᵗ {f = []} {g = []} {h = []} = []
  assocᵗ {f = []} {g = []} {h = y ∷ʳ _} = y ∷ʳ assocᵗ
  assocᵗ {f = []} {g = _ ∷ʳ _} {h = y ∷ʳ _} = y ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ʳ _} {g = _ ∷ʳ _} {h = y ∷ʳ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ _} {g = _ ∷ʳ _} {h = y ∷ʳ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ʳ _} {g = _ ∷ _} {h = y ∷ʳ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ _} {g = _ ∷ _} {h = y ∷ʳ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = []} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ʳ _} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ _} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ʳ _} {g = _ ∷ _} {h = _ ∷ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ _} {g = _ ∷ _} {h = _ ∷ _} = assoc ∷ assocᵗ

  sym-assocᵗ : ∀ {W X Y Z : List Obj} {f : Sublist _⇒_ W X} {g : Sublist _⇒_ X Y} {h : Sublist _⇒_ Y Z}
             → trans (flip _∘_) (trans (flip _∘_) f g) h ≈ᵗ trans (flip _∘_) f (trans (flip _∘_) g h)
  sym-assocᵗ {f = []} {g = []} {h = []} = []
  sym-assocᵗ {f = []} {g = []} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = []} {g = _ ∷ʳ _} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ʳ _} {g = _ ∷ʳ _} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ _} {g = _ ∷ʳ _} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ʳ _} {g = _ ∷ _} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ _} {g = _ ∷ _} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = []} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ʳ _} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ _} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ʳ _} {g = _ ∷ _} {h = _ ∷ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ _} {g = _ ∷ _} {h = _ ∷ _} = sym-assoc ∷ sym-assocᵗ

  -- dsp: lemmas
  identityˡᵗ-gap0 : {X : List Obj} → {Y : List Obj} → {f : Sublist _⇒_ X Y} → trans (flip _∘_) f (refl id) ≈ᵗ f
  identityˡᵗ-gap0 {f = []} = []
  identityˡᵗ-gap0 {f = y ∷ʳ fs} = y ∷ʳ identityˡᵗ-gap0
  identityˡᵗ-gap0 {f = _ ∷ fs} = identityˡ ∷ identityˡᵗ-gap0

  -- dsp: end of lemmas
  identityˡᵗ : ∀ {X Y} {f : Sublist _⇒_ X Y} → trans (flip _∘_) f (refl id) ≈ᵗ f
  identityˡᵗ = identityˡᵗ-gap0
