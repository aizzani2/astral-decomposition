------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic products of binary relations
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a (non-strict) partial order.

{-# OPTIONS --without-K #-}

module Data.Product.Relation.Binary.Lex.NonStrict where

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as Pointwise
  using (Pointwise)
import Data.Product.Relation.Binary.Lex.Strict as Strict
open import Data.Sum.Base using (inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles
  using (Poset; DecTotalOrder; TotalOrder)
open import Relation.Binary.Structures
  using (IsPartialOrder; IsEquivalence; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Transitive; Symmetric; Decidable; Antisymmetric; Total; Trichotomous
        ; Irreflexive; Asymmetric; _Respects₂_; tri<; tri>; tri≈)
open import Relation.Binary.Consequences
import Relation.Binary.Construct.NonStrictToStrict as Conv


private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

×-Lex : (_≈₁_ : Rel A ℓ₁) (_≤₁_ : Rel A ℓ₂) (_≤₂_ : Rel B ℓ₃) →
        Rel (A × B) _
×-Lex _≈₁_ _≤₁_ _≤₂_ = Strict.×-Lex _≈₁_ (Conv._<_ _≈₁_ _≤₁_) _≤₂_

------------------------------------------------------------------------
-- Properties

module _ {_≈₁_ : Rel A ℓ₁} {_≤₁_ : Rel A ℓ₂} {_≤₂_ : Rel B ℓ₃} where

  private
    _≤ₗₑₓ_ = ×-Lex _≈₁_ _≤₁_ _≤₂_

  ×-decidable : Decidable _≈₁_ → Decidable _≤₁_ → Decidable _≤₂_ →
                Decidable _≤ₗₑₓ_
  ×-decidable dec-≈₁ dec-≤₁ dec-≤₂ =
    Strict.×-decidable dec-≈₁ (Conv.<-decidable _ _ dec-≈₁ dec-≤₁)
                       dec-≤₂

module _ {_≈₁_ : Rel A ℓ₁} {_≤₁_ : Rel A ℓ₂}
         {_≈₂_ : Rel B ℓ₃} {_≤₂_ : Rel B ℓ₄}
         where

  private
    _≤ₗₑₓ_ = ×-Lex _≈₁_ _≤₁_ _≤₂_
    _≋_    = Pointwise _≈₁_ _≈₂_

  ×-respects₂ : IsEquivalence _≈₁_ →
                _≤₁_ Respects₂ _≈₁_ → _≤₂_ Respects₂ _≈₂_ →
                _≤ₗₑₓ_ Respects₂ _≋_
  ×-respects₂ eq₁ resp₁ resp₂ =
    Strict.×-respects₂ eq₁ (Conv.<-resp-≈ _ _ eq₁ resp₁) resp₂


------------------------------------------------------------------------
-- Structures

  -- dsp: lemmas
  -- dsp: end of lemmas
  ×-isTotalOrder : Decidable _≈₁_ →
                   IsTotalOrder _≈₁_ _≤₁_ →
                   IsTotalOrder _≈₂_ _≤₂_ →
                   IsTotalOrder _≋_ _≤ₗₑₓ_
  ×-isTotalOrder dec-≈₁ isTotalOrder₁ isTotalOrder₂ =
    {!!}
