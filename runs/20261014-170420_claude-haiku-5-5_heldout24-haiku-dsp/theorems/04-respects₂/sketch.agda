------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

-- The definitions of lexicographic ordering used here are suitable if
-- the argument order is a strict partial order.

{-# OPTIONS --without-K #-}

module Data.List.Relation.Binary.Lex.Strict where

open import Function.Base using (_∘_; id)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_)
open import Level using (_⊔_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles
  using (StrictPartialOrder; StrictTotalOrder; Preorder; Poset; DecPoset; DecTotalOrder)
open import Relation.Binary.Structures
  using (IsEquivalence; IsStrictPartialOrder; IsStrictTotalOrder; IsPreorder; IsPartialOrder; IsDecPartialOrder; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Irreflexive; Symmetric; _Respects₂_; Total; Asymmetric; Antisymmetric; Transitive; Trichotomous; Decidable; tri≈; tri<; tri>)
open import Relation.Binary.Consequences
open import Data.List.Relation.Binary.Pointwise as Pointwise
   using (Pointwise; []; _∷_; head; tail)

import Data.List.Relation.Binary.Lex as Core

------------------------------------------------------------------------
-- Re-exporting core definitions

open Core public
  using (Lex-<; Lex-≤; base; halt; this; next; ¬≤-this; ¬≤-next)

------------------------------------------------------------------------
-- Strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  -- Properties

  module _ {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

    private
      _≋_ = Pointwise _≈_
      _<_ = Lex-< _≈_ _≺_

    xs≮[] : ∀ {xs} → ¬ xs < []
    xs≮[] (base ())

    ¬[]<[] : ¬ [] < []
    ¬[]<[] = xs≮[]

    <-irreflexive : Irreflexive _≈_ _≺_ → Irreflexive _≋_ _<_
    <-irreflexive irr (x≈y ∷ xs≋ys) (this x<y)     = irr x≈y x<y
    <-irreflexive irr (x≈y ∷ xs≋ys) (next _ xs⊴ys) =
      <-irreflexive irr xs≋ys xs⊴ys

    <-asymmetric : Symmetric _≈_ → _≺_ Respects₂ _≈_ → Asymmetric _≺_ →
                   Asymmetric _<_
    <-asymmetric sym resp as = asym
      where
      irrefl : Irreflexive _≈_ _≺_
      irrefl = asym⇒irr resp sym as

      asym : Asymmetric _<_
      asym (base bot)       _                = bot
      asym (this x<y)       (this y<x)       = as x<y y<x
      asym (this x<y)       (next y≈x ys⊴xs) = irrefl (sym y≈x) x<y
      asym (next x≈y xs⊴ys) (this y<x)       = irrefl (sym x≈y) y<x
      asym (next x≈y xs⊴ys) (next y≈x ys⊴xs) = asym xs⊴ys ys⊴xs

    <-antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _≺_ →
                      Asymmetric _≺_ → Antisymmetric _≋_ _<_
    <-antisymmetric = Core.antisymmetric

    <-transitive : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ →
                   Transitive _≺_ → Transitive _<_
    <-transitive = Core.transitive

    <-compare : Symmetric _≈_ → Trichotomous _≈_ _≺_ →
                Trichotomous _≋_ _<_
    <-compare sym tri []       []       = tri≈ ¬[]<[] []    ¬[]<[]
    <-compare sym tri []       (y ∷ ys) = tri< halt   (λ()) (λ())
    <-compare sym tri (x ∷ xs) []       = tri> (λ())  (λ()) halt
    <-compare sym tri (x ∷ xs) (y ∷ ys) with tri x y
    ... | tri< x<y x≉y y≮x =
          tri< (this x<y) (x≉y ∘ head) (¬≤-this (x≉y ∘ sym) y≮x)
    ... | tri> x≮y x≉y y<x =
          tri> (¬≤-this x≉y x≮y) (x≉y ∘ head) (this y<x)
    ... | tri≈ x≮y x≈y y≮x with <-compare sym tri xs ys
    ...   | tri< xs<ys xs≉ys ys≮xs =
            tri< (next x≈y xs<ys) (xs≉ys ∘ tail) (¬≤-next y≮x ys≮xs)
    ...   | tri≈ xs≮ys xs≈ys ys≮xs =
            tri≈ (¬≤-next x≮y xs≮ys) (x≈y ∷ xs≈ys) (¬≤-next y≮x ys≮xs)
    ...   | tri> xs≮ys xs≉ys ys<xs =
            tri> (¬≤-next x≮y xs≮ys) (xs≉ys ∘ tail) (next (sym x≈y) ys<xs)

    <-decidable : Decidable _≈_ → Decidable _≺_ → Decidable _<_
    <-decidable = Core.decidable (no id)

    -- dsp: lemmas
    postulate
      ≋-sym : Symmetric _≈_ → Symmetric _≋_

    postulate
      <-left-respects : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → (xs ys zs : List A) → xs ≋ ys → xs < zs → ys < zs

    postulate
      <-right-respects : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → (xs ys zs : List A) → zs < xs → xs ≋ ys → zs < ys

    -- dsp: end of lemmas
    <-respects₂ : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → _<_ Respects₂ _≋_
    <-respects₂ eq resp =
      -- Step 12 (forward direction): suppose xs ≋ ys. If xs < zs, then ys < zs by the left-respect lemma.
      (λ xs≋ys xs<zs → {!!})
      -- Step 13 (forward direction): suppose xs ≋ ys. If zs < xs, then zs < ys by the right-respect lemma.
      , (λ zs<xs xs≋ys → {!!})
