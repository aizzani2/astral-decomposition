------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of reflexive closures
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Relation.Binary.Construct.Closure.Reflexive.Properties where

open import Data.Product.Base as Product using (_,_; map)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Function.Base using (id)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel; REL; _=[_]⇒_)
open import Relation.Binary.Structures
  using (IsPreorder; IsStrictPartialOrder; IsPartialOrder
        ; IsDecStrictPartialOrder; IsDecPartialOrder; IsStrictTotalOrder
        ; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Symmetric; Transitive; Reflexive; Asymmetric; Antisymmetric
        ; Trichotomous; Total; Decidable; DecidableEquality; tri<; tri≈; tri>
        ; _Respectsˡ_; _Respectsʳ_; _Respects_; _Respects₂_)
open import Relation.Binary.Construct.Closure.Reflexive
  using (ReflClosure; [_]; refl)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Nullary.Decidable as Dec using (yes; no)
open import Relation.Unary using (Pred)

private
  variable
    a b ℓ p q : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Relational properties

module _ {P : Rel A p} {Q : Rel B q} where

  =[]⇒ : ∀ {f : A → B} → P =[ f ]⇒ Q → ReflClosure P =[ f ]⇒ ReflClosure Q
  =[]⇒ x [ x∼y ] = [ x x∼y ]
  =[]⇒ x refl    = refl

module _ {_~_ : Rel A ℓ} where

  private
    _~ᵒ_ = ReflClosure _~_

  fromSum : ∀ {x y} → x ≡ y ⊎ x ~ y → x ~ᵒ y
  fromSum (inj₁ refl) = refl
  fromSum (inj₂ y) = [ y ]

  toSum : ∀ {x y} → x ~ᵒ y → x ≡ y ⊎ x ~ y
  toSum [ x∼y ] = inj₂ x∼y
  toSum refl = inj₁ refl

  ⊎⇔Refl : ∀ {a b} → (a ≡ b ⊎ a ~ b) ⇔ a ~ᵒ b
  ⊎⇔Refl = mk⇔ fromSum toSum

  sym : Symmetric _~_ → Symmetric _~ᵒ_
  sym ~-sym [ x∼y ] = [ ~-sym x∼y ]
  sym ~-sym refl    = refl

  -- dsp: lemmas
  -- dsp: end of lemmas
  trans : Transitive _~_ → Transitive _~ᵒ_
  trans ~-trans [ x∼y ] [ y∼z ] = [ ~-trans x∼y y∼z ]
  trans ~-trans [ x∼y ] refl    = [ x∼y ]
  trans ~-trans refl    y∼z     = y∼z
