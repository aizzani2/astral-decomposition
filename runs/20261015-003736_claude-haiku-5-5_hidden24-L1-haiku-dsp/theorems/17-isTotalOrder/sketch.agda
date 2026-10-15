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

×-reflexive : (_≈₁_ : Rel A ℓ₁) (_≤₁_ : Rel A ℓ₂)
              {_≈₂_ : Rel B ℓ₃} (_≤₂_ : Rel B ℓ₄) →
              _≈₂_ ⇒ _≤₂_ →
              (Pointwise _≈₁_ _≈₂_) ⇒ (×-Lex _≈₁_ _≤₁_ _≤₂_)
×-reflexive _≈₁_ _≤₁_ _≤₂_ refl₂ =
  Strict.×-reflexive _≈₁_ (Conv._<_ _≈₁_ _≤₁_) _≤₂_ refl₂

module _ {_≈₁_ : Rel A ℓ₁} {_≤₁_ : Rel A ℓ₂} {_≤₂_ : Rel B ℓ₃} where

  private
    _≤ₗₑₓ_ = ×-Lex _≈₁_ _≤₁_ _≤₂_

  ×-transitive : IsPartialOrder _≈₁_ _≤₁_ → Transitive _≤₂_ →
                 Transitive _≤ₗₑₓ_
  ×-transitive po₁ trans₂ =
    Strict.×-transitive {_≈₁_ = _≈₁_} {_<₂_ = _≤₂_}
      isEquivalence (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
      (Conv.<-trans _ _ po₁)
      trans₂
    where open IsPartialOrder po₁

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

  ×-antisymmetric : IsPartialOrder _≈₁_ _≤₁_ → Antisymmetric _≈₂_ _≤₂_ →
                   Antisymmetric _≋_ _≤ₗₑₓ_
  ×-antisymmetric po₁ antisym₂ =
    Strict.×-antisymmetric {_≈₁_ = _≈₁_} {_<₂_ = _≤₂_}
       ≈-sym₁ irrefl₁ asym₁ antisym₂
    where
    open IsPartialOrder po₁
    open Eq renaming (refl to ≈-refl₁; sym to ≈-sym₁)

    irrefl₁ : Irreflexive _≈₁_ (Conv._<_ _≈₁_ _≤₁_)
    irrefl₁ = Conv.<-irrefl _≈₁_ _≤₁_

    asym₁ : Asymmetric (Conv._<_ _≈₁_ _≤₁_)
    asym₁ = trans∧irr⇒asym {_≈_ = _≈₁_}
                           ≈-refl₁ (Conv.<-trans _ _ po₁) irrefl₁

  ×-respects₂ : IsEquivalence _≈₁_ →
                _≤₁_ Respects₂ _≈₁_ → _≤₂_ Respects₂ _≈₂_ →
                _≤ₗₑₓ_ Respects₂ _≋_
  ×-respects₂ eq₁ resp₁ resp₂ =
    Strict.×-respects₂ eq₁ (Conv.<-resp-≈ _ _ eq₁ resp₁) resp₂


------------------------------------------------------------------------
-- Structures

  -- dsp: lemmas
  postulate
    ≋-isEquivalence : IsEquivalence _≈₁_ → IsEquivalence _≈₂_ → IsEquivalence _≋_

  postulate
    ×-lex-resp-left : IsEquivalence _≈₁_ → _≤₁_ Respects₂ _≈₁_ → _≤₂_ Respects₂ _≈₂_ → ∀ {p q r : A × B} → p ≋ q → p ≤ₗₑₓ r → q ≤ₗₑₓ r

  postulate
    ×-lex-resp-right : IsEquivalence _≈₁_ → _≤₁_ Respects₂ _≈₁_ → _≤₂_ Respects₂ _≈₂_ → ∀ {p q r : A × B} → p ≤ₗₑₓ q → q ≋ r → p ≤ₗₑₓ r

  postulate
    ×-lex-refl : _≈₂_ ⇒ _≤₂_ → ∀ {p q : A × B} → p ≋ q → p ≤ₗₑₓ q

  postulate
    ×-lex-trans : IsPartialOrder _≈₁_ _≤₁_ → _≤₁_ Respects₂ _≈₁_ → Transitive _≤₂_ → ∀ {p q r : A × B} → p ≤ₗₑₓ q → q ≤ₗₑₓ r → p ≤ₗₑₓ r

  postulate
    ×-lex-antisymm : IsPartialOrder _≈₁_ _≤₁_ → Antisymmetric _≈₂_ _≤₂_ → ∀ {p q : A × B} → p ≤ₗₑₓ q → q ≤ₗₑₓ p → p ≋ q

  postulate
    ×-lex-total : Decidable _≈₁_ → Total _≤₁_ → Total _≤₂_ → Total _≤ₗₑₓ_

  -- dsp: end of lemmas
  ×-isTotalOrder : Decidable _≈₁_ → IsTotalOrder _≈₁_ _≤₁_ → IsTotalOrder _≈₂_ _≤₂_ → IsTotalOrder _≋_ _≤ₗₑₓ_
  -- Step 1: ≤_lex is reflexive, transitive, antisymmetric and total with respect to ≈_pw, and respects ≈_pw.
  ×-isTotalOrder dec-≈₁ tot₁ tot₂ = record
    { isPartialOrder = record
        { isPreorder = record
            -- Step 2: ≈_pw is an equivalence relation on A × B.
            { isEquivalence = record
                -- Step 3: reflexivity: for any (a,b), (a,b) ≈_pw (a,b).
                { refl = {!!}
                -- Step 4: symmetry: from (a,b) ≈_pw (a',b') infer (a',b') ≈_pw (a,b).
                ; sym = {!!}
                -- Step 5: transitivity: from (a,b) ≈_pw (a',b') and (a',b') ≈_pw (a'',b'') infer (a,b) ≈_pw (a'',b'').
                ; trans = {!!}
                }
            -- Step 14-15: for every (a,b), (a,b) ≤_lex (a,b).
            ; reflexive = {!!}
            -- Step 16: if (a,b) ≤_lex (c,d) and (c,d) ≤_lex (e,f), then (a,b) ≤_lex (e,f).
            ; trans = {!!}
            }
        -- Step 21: if (a,b) ≤_lex (c,d) and (c,d) ≤_lex (a,b), then (a,b) ≈_pw (c,d).
        ; antisym = {!!}
        }
    -- Step 26: assuming ≈₁ is decidable, either (a,b) ≤_lex (c,d) or (c,d) ≤_lex (a,b).
    ; total = {!!}
    }
