------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic properties of ℕᵇ
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Nat.Binary.Properties where

open import Algebra.Bundles
  using (Magma; Monoid; CommutativeMonoid; Semigroup; CommutativeSemigroup
        ; Semiring; CommutativeSemiring)
open import Algebra.Morphism.Structures
import Algebra.Morphism.MonoidMonomorphism as MonoidMonomorphism
open import Algebra.Consequences.Propositional using (comm∧distrˡ⇒distrʳ)
open import Data.Bool.Base using (if_then_else_; Bool; true; false)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Binary.Base
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s; s<s⁻¹)
open import Data.Nat.DivMod using (_%_; _/_; m/n≤m; +-distrib-/-∣ˡ)
open import Data.Nat.Divisibility using (∣-refl)
import Data.Nat.Properties as ℕ
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; _$_; id)
open import Function.Definitions using (Injective; Surjective;
  Inverseˡ; Inverseʳ; Inverseᵇ)
open import Function.Consequences.Propositional
 using (strictlySurjective⇒surjective; strictlyInverseˡ⇒inverseˡ
        ; strictlyInverseʳ⇒inverseʳ)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.Consequences using (trans∧irr⇒asym; tri⇒dec<)
open import Relation.Binary.Morphism
  using (IsRelHomomorphism; IsOrderHomomorphism; IsOrderMonomorphism)
import Relation.Binary.Morphism.OrderMonomorphism as OrderMonomorphism
open import Relation.Binary.PropositionalEquality.Algebra
  using (magma; isMagma)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; cong; cong₂; sym; _≗_; trans; ≢-sym; subst₂;
        subst; resp₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence; setoid; decSetoid; module ≡-Reasoning;
         isEquivalence)
open import Relation.Nullary using (¬_; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation.Core using (contradiction)

open import Algebra.Definitions {A = ℕᵇ} _≡_
open import Algebra.Structures {A = ℕᵇ} _≡_
import Algebra.Properties.CommutativeSemigroup as CommSemigProp
import Algebra.Properties.CommutativeSemigroup ℕ.+-commutativeSemigroup
  as ℕ-+-semigroupProperties
import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_
  as StrictToNonStrict
open +-*-Solver

private
  variable
    x : ℕᵇ

infix 4  _<?_ _≡?_ _≤?_

------------------------------------------------------------------------
-- Properties of _≡_
------------------------------------------------------------------------

2[1+x]≢0 : 2[1+ x ] ≢ 0ᵇ
2[1+x]≢0 ()

1+[2x]≢0 : 1+[2 x ] ≢ 0ᵇ
1+[2x]≢0 ()

2[1+_]-injective : Injective _≡_ _≡_ 2[1+_]
2[1+_]-injective refl = refl

1+[2_]-injective : Injective _≡_ _≡_ 1+[2_]
1+[2_]-injective refl = refl

_≡?_ : DecidableEquality ℕᵇ
zero     ≡? zero     =  yes refl
zero     ≡? 2[1+ _ ] =  no λ()
zero     ≡? 1+[2 _ ] =  no λ()
2[1+ _ ] ≡? zero     =  no λ()
2[1+ x ] ≡? 2[1+ y ] =  Dec.map′ (cong 2[1+_]) 2[1+_]-injective (x ≡? y)
2[1+ _ ] ≡? 1+[2 _ ] =  no λ()
1+[2 _ ] ≡? zero     =  no λ()
1+[2 _ ] ≡? 2[1+ _ ] =  no λ()
1+[2 x ] ≡? 1+[2 y ] =  Dec.map′ (cong 1+[2_]) 1+[2_]-injective (x ≡? y)

≡-isDecEquivalence : IsDecEquivalence {A = ℕᵇ} _≡_
≡-isDecEquivalence = isDecEquivalence _≡?_

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid ℕᵇ

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≡?_

------------------------------------------------------------------------
-- Properties of toℕ & fromℕ
------------------------------------------------------------------------

toℕ-double : ∀ x → toℕ (double x) ≡ 2 ℕ.* (toℕ x)
toℕ-double zero     =  refl
toℕ-double 1+[2 x ] =  cong ((2 ℕ.*_) ∘ ℕ.suc) (toℕ-double x)
toℕ-double 2[1+ x ] =  cong (2 ℕ.*_) (sym (ℕ.*-distribˡ-+ 2 1 (toℕ x)))

toℕ-suc : ∀ x → toℕ (suc x) ≡ ℕ.suc (toℕ x)
toℕ-suc zero     =  refl
toℕ-suc 2[1+ x ] =  cong (ℕ.suc ∘ (2 ℕ.*_)) (toℕ-suc x)
toℕ-suc 1+[2 x ] =  ℕ.*-distribˡ-+ 2 1 (toℕ x)

toℕ-pred : ∀ x → toℕ (pred x) ≡ ℕ.pred (toℕ x)
toℕ-pred zero     =  refl
toℕ-pred 2[1+ x ] =  cong ℕ.pred $ sym $ ℕ.*-distribˡ-+ 2 1 (toℕ x)
toℕ-pred 1+[2 x ] =  toℕ-double x

toℕ-injective : Injective _≡_ _≡_ toℕ
toℕ-injective {zero}     {zero}     _               =  refl
toℕ-injective {2[1+ x ]} {2[1+ y ]} 2[1+xN]≡2[1+yN] =  cong 2[1+_] x≡y
  where
  1+xN≡1+yN = ℕ.*-cancelˡ-≡ (ℕ.suc _) (ℕ.suc _) 2 2[1+xN]≡2[1+yN]
  xN≡yN     = cong ℕ.pred 1+xN≡1+yN
  x≡y       = toℕ-injective xN≡yN

toℕ-injective {2[1+ x ]} {1+[2 y ]} 2[1+xN]≡1+2yN =
  contradiction 2[1+xN]≡1+2yN (ℕ.even≢odd (ℕ.suc (toℕ x)) (toℕ y))

toℕ-injective {1+[2 x ]} {2[1+ y ]} 1+2xN≡2[1+yN] =
  contradiction (sym 1+2xN≡2[1+yN]) (ℕ.even≢odd (ℕ.suc (toℕ y)) (toℕ x))

toℕ-injective {1+[2 x ]} {1+[2 y ]} 1+2xN≡1+2yN =  cong 1+[2_] x≡y
  where
  2xN≡2yN = cong ℕ.pred 1+2xN≡1+2yN
  xN≡yN   = ℕ.*-cancelˡ-≡ _ _ 2 2xN≡2yN
  x≡y     = toℕ-injective xN≡yN

toℕ-isRelHomomorphism : IsRelHomomorphism _≡_ _≡_ toℕ
toℕ-isRelHomomorphism = record
  { cong = cong toℕ
  }

-- dsp: lemmas
-- dsp: end of lemmas
toℕ-inverseˡ : Inverseˡ _≡_ _≡_ toℕ fromℕ
toℕ-inverseˡ x = {!!}
