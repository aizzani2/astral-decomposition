------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about parities
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Parity.Properties where

open import Algebra.Bundles
open import Data.Nat.Base as ℕ using (zero; suc; parity)
open import Data.Parity.Base as ℙ using (Parity; 0ℙ; 1ℙ; _⁻¹; toSign; fromSign)
open import Data.Product.Base using (_,_)
open import Data.Sign.Base as 𝕊
  using (Sign; +; -; _*_; opposite; *-rawMagma; *-1-rawMonoid; *-1-rawGroup)
open import Function.Base using (_$_; id)
open import Function.Definitions
  using (Injective; Surjective; Inverseʳ; Inverseˡ)
open import Function.Consequences.Propositional
  using (inverseʳ⇒injective; inverseˡ⇒surjective)
open import Level using (0ℓ)
open import Relation.Binary
  using (Decidable; DecidableEquality; Setoid; DecSetoid; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning; setoid; isEquivalence; decSetoid; isDecEquivalence)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)

open import Algebra.Structures {A = Parity} _≡_
open import Algebra.Definitions {A = Parity} _≡_
open import Algebra.Consequences.Propositional
  using (selfInverse⇒involutive; selfInverse⇒injective; comm∧distrˡ⇒distrʳ)
open import Algebra.Morphism.Structures

------------------------------------------------------------------------
-- Equality

infix 4 _≡?_

_≡?_ : DecidableEquality Parity
1ℙ ≡? 1ℙ = yes refl
1ℙ ≡? 0ℙ = no λ()
0ℙ ≡? 1ℙ = no λ()
0ℙ ≡? 0ℙ = yes refl

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid Parity

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≡?_

≡-isDecEquivalence : IsDecEquivalence _≡_
≡-isDecEquivalence = isDecEquivalence _≡?_

------------------------------------------------------------------------
-- _⁻¹

-- Algebraic properties of _⁻¹

⁻¹-selfInverse : SelfInverse _⁻¹
⁻¹-selfInverse { 1ℙ } { 0ℙ } refl = refl
⁻¹-selfInverse { 0ℙ } { 1ℙ } refl = refl

⁻¹-involutive : Involutive _⁻¹
⁻¹-involutive = selfInverse⇒involutive ⁻¹-selfInverse

⁻¹-injective : Injective _≡_ _≡_ _⁻¹
⁻¹-injective = selfInverse⇒injective ⁻¹-selfInverse

------------------------------------------------------------------------
-- other properties of _⁻¹

p≢p⁻¹ : ∀ p → p ≢ p ⁻¹
p≢p⁻¹ 1ℙ ()
p≢p⁻¹ 0ℙ ()

------------------------------------------------------------------------
-- ⁻¹ and _+_

p+p⁻¹≡1ℙ : ∀ p → p ℙ.+ p ⁻¹ ≡ 1ℙ
p+p⁻¹≡1ℙ 0ℙ = refl
p+p⁻¹≡1ℙ 1ℙ = refl

p⁻¹+p≡1ℙ : ∀ p → p ⁻¹ ℙ.+ p ≡ 1ℙ
p⁻¹+p≡1ℙ 0ℙ = refl
p⁻¹+p≡1ℙ 1ℙ = refl

------------------------------------------------------------------------
-- ⁻¹ and _*_

p*p⁻¹≡0ℙ : ∀ p → p ℙ.* p ⁻¹ ≡ 0ℙ
p*p⁻¹≡0ℙ 0ℙ = refl
p*p⁻¹≡0ℙ 1ℙ = refl

p⁻¹*p≡0ℙ : ∀ p → p ⁻¹ ℙ.* p ≡ 0ℙ
p⁻¹*p≡0ℙ 0ℙ = refl
p⁻¹*p≡0ℙ 1ℙ = refl

------------------------------------------------------------------------
-- _+_

-- Algebraic properties of _+_

p+p≡0ℙ : ∀ p → p ℙ.+ p ≡ 0ℙ
p+p≡0ℙ 0ℙ = refl
p+p≡0ℙ 1ℙ = refl

+-identityˡ : LeftIdentity 0ℙ ℙ._+_
+-identityˡ _ = refl

+-identityʳ : RightIdentity 0ℙ ℙ._+_
+-identityʳ 1ℙ = refl
+-identityʳ 0ℙ = refl

+-identity : Identity 0ℙ ℙ._+_
+-identity = +-identityˡ  , +-identityʳ

+-comm : Commutative ℙ._+_
+-comm 0ℙ 0ℙ = refl
+-comm 0ℙ 1ℙ = refl
+-comm 1ℙ 0ℙ = refl
+-comm 1ℙ 1ℙ = refl

+-assoc : Associative ℙ._+_
+-assoc 0ℙ 0ℙ _ = refl
+-assoc 0ℙ 1ℙ _ = refl
+-assoc 1ℙ 0ℙ _ = refl
+-assoc 1ℙ 1ℙ 0ℙ = refl
+-assoc 1ℙ 1ℙ 1ℙ = refl

+-cancelʳ-≡ : RightCancellative ℙ._+_
+-cancelʳ-≡ _ 1ℙ 1ℙ _  = refl
+-cancelʳ-≡ _ 1ℙ 0ℙ eq = contradiction (sym eq) (p≢p⁻¹ _)
+-cancelʳ-≡ _ 0ℙ 1ℙ eq = contradiction eq (p≢p⁻¹ _)
+-cancelʳ-≡ _ 0ℙ 0ℙ _  = refl

+-cancelˡ-≡ : LeftCancellative ℙ._+_
+-cancelˡ-≡ 1ℙ _ _ eq = ⁻¹-injective eq
+-cancelˡ-≡ 0ℙ _ _ eq = eq

+-cancel-≡ : Cancellative ℙ._+_
+-cancel-≡ = +-cancelˡ-≡ , +-cancelʳ-≡

+-inverse : Inverse 0ℙ id ℙ._+_
+-inverse = p+p≡0ℙ , p+p≡0ℙ

------------------------------------------------------------------------
-- Bundles

+-isMagma : IsMagma ℙ._+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ ℙ._+_
  }

+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-isSemigroup : IsSemigroup ℙ._+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-isCommutativeSemigroup : IsCommutativeSemigroup ℙ._+_
+-isCommutativeSemigroup = record
  { isSemigroup = +-isSemigroup
  ; comm = +-comm
  }

+-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
+-commutativeSemigroup = record
  { isCommutativeSemigroup = +-isCommutativeSemigroup
  }

+-0-isMonoid : IsMonoid ℙ._+_ 0ℙ
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid ℙ._+_ 0ℙ
+-0-isCommutativeMonoid = record
   { isMonoid = +-0-isMonoid
   ; comm = +-comm
   }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

+-0-isGroup : IsGroup ℙ._+_ 0ℙ id
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse = +-inverse
  ; ⁻¹-cong = id
  }

+-0-group : Group 0ℓ 0ℓ
+-0-group = record
  { isGroup = +-0-isGroup
  }

+-0-isAbelianGroup : IsAbelianGroup ℙ._+_ 0ℙ id
+-0-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm = +-comm
  }

+-0-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup = record
  { isAbelianGroup = +-0-isAbelianGroup
  }

------------------------------------------------------------------------
-- _*_

-- Algebraic properties of _*_

*-idem : Idempotent ℙ._*_
*-idem 0ℙ = refl
*-idem 1ℙ = refl

*-assoc : Associative ℙ._*_
*-assoc 0ℙ 0ℙ _ = refl
*-assoc 0ℙ 1ℙ _ = refl
*-assoc 1ℙ 0ℙ _ = refl
*-assoc 1ℙ 1ℙ 0ℙ = refl
*-assoc 1ℙ 1ℙ 1ℙ = refl

*-distribˡ-+ : ℙ._*_ DistributesOverˡ ℙ._+_
*-distribˡ-+ 0ℙ q r = refl
*-distribˡ-+ 1ℙ 0ℙ 0ℙ = refl
*-distribˡ-+ 1ℙ 0ℙ 1ℙ = refl
*-distribˡ-+ 1ℙ 1ℙ 0ℙ = refl
*-distribˡ-+ 1ℙ 1ℙ 1ℙ = refl

-- dsp: lemmas
-- dsp: end of lemmas
*-zero : Zero 0ℙ ℙ._*_
*-zero = (λ { 0ℙ → refl ; 1ℙ → refl }) , (λ { 0ℙ → refl ; 1ℙ → refl })
