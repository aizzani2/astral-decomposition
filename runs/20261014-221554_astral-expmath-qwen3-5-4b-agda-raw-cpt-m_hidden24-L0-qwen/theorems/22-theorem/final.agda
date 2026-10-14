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

toℕ-fromℕ' : toℕ ∘ fromℕ' ≗ id
toℕ-fromℕ' 0         = refl
toℕ-fromℕ' (ℕ.suc n) = begin
  toℕ (fromℕ' (ℕ.suc n))   ≡⟨⟩
  toℕ (suc (fromℕ' n))     ≡⟨ toℕ-suc (fromℕ' n) ⟩
  ℕ.suc (toℕ (fromℕ' n))   ≡⟨ cong ℕ.suc (toℕ-fromℕ' n) ⟩
  ℕ.suc n                 ∎
  where open ≡-Reasoning

fromℕ≡fromℕ' : fromℕ ≗ fromℕ'
fromℕ≡fromℕ' n = fromℕ-helper≡fromℕ' n n ℕ.≤-refl
  where
  split : ℕᵇ → Maybe Bool × ℕᵇ
  split zero     = nothing , zero
  split 2[1+ n ] = just false , n
  split 1+[2 n ] = just true , n

  head = proj₁ ∘ split
  tail = proj₂ ∘ split

  split-injective : Injective _≡_ _≡_ split
  split-injective {zero} {zero} refl = refl
  split-injective {2[1+ _ ]} {2[1+ _ ]} refl = refl
  split-injective {1+[2 _ ]} {1+[2 _ ]} refl = refl

  split-if : ∀ x xs → split (if x then 1+[2 xs ] else 2[1+ xs ]) ≡ (just x , xs)
  split-if false xs = refl
  split-if true xs = refl

  head-suc : ∀ n → head (suc (suc (suc n))) ≡ head (suc n)
  head-suc zero = refl
  head-suc 2[1+ n ] = refl
  head-suc 1+[2 n ] = refl

  tail-suc : ∀ n → suc (tail (suc n)) ≡ tail (suc (suc (suc n)))
  tail-suc zero = refl
  tail-suc 2[1+ n ] = refl
  tail-suc 1+[2 n ] = refl

  head-homo : ∀ n → head (suc (fromℕ' n)) ≡ just (n % 2 ℕ.≡ᵇ 0)
  head-homo ℕ.zero = refl
  head-homo (ℕ.suc ℕ.zero) = refl
  head-homo (ℕ.suc (ℕ.suc n)) = trans (head-suc (fromℕ' n)) (head-homo n)

  open ≡-Reasoning

  tail-homo : ∀ n → tail (suc (fromℕ' n)) ≡ fromℕ' (n / 2)
  tail-homo ℕ.zero = refl
  tail-homo (ℕ.suc ℕ.zero) = refl
  tail-homo (ℕ.suc (ℕ.suc n)) = begin
    tail (suc (fromℕ' (ℕ.suc (ℕ.suc n))))  ≡⟨ tail-suc (fromℕ' n) ⟨
    suc (tail (suc (fromℕ' n)))            ≡⟨ cong suc (tail-homo n) ⟩
    fromℕ' (ℕ.suc (n / 2))                 ≡⟨ cong fromℕ' (+-distrib-/-∣ˡ {2} n ∣-refl) ⟨
    fromℕ' (ℕ.suc (ℕ.suc n) / 2)           ∎

  fromℕ-helper≡fromℕ' : ∀ n w → n ℕ.≤ w → fromℕ.helper n n w ≡ fromℕ' n
  fromℕ-helper≡fromℕ' ℕ.zero w p = refl
  fromℕ-helper≡fromℕ' (ℕ.suc n) (ℕ.suc w) (s≤s n≤w) =
    split-injective (begin
      split (fromℕ.helper n (ℕ.suc n) (ℕ.suc w))         ≡⟨ split-if _ _ ⟩
      just (n % 2 ℕ.≡ᵇ 0) , fromℕ.helper n (n / 2) w     ≡⟨ cong (_ ,_) rec-n/2 ⟩
      just (n % 2 ℕ.≡ᵇ 0) , fromℕ' (n / 2)               ≡⟨ cong₂ _,_ (head-homo n) (tail-homo n) ⟨
      head (fromℕ' (ℕ.suc n)) , tail (fromℕ' (ℕ.suc n))  ≡⟨⟩
      split (fromℕ' (ℕ.suc n))                           ∎)
    where rec-n/2 = fromℕ-helper≡fromℕ' (n / 2) w (ℕ.≤-trans (m/n≤m n 2) n≤w)

toℕ-fromℕ : toℕ ∘ fromℕ ≗ id
toℕ-fromℕ n rewrite fromℕ≡fromℕ' n = toℕ-fromℕ' n

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

toℕ-surjective : Surjective _≡_ _≡_ toℕ
toℕ-surjective = strictlySurjective⇒surjective (λ n → fromℕ n , toℕ-fromℕ n)

toℕ-isRelHomomorphism : IsRelHomomorphism _≡_ _≡_ toℕ
toℕ-isRelHomomorphism = record
  { cong = cong toℕ
  }

fromℕ-injective : Injective _≡_ _≡_ fromℕ
fromℕ-injective {x} {y} f[x]≡f[y] = begin
  x             ≡⟨ sym (toℕ-fromℕ x) ⟩
  toℕ (fromℕ x) ≡⟨ cong toℕ f[x]≡f[y] ⟩
  toℕ (fromℕ y) ≡⟨ toℕ-fromℕ y ⟩
  y             ∎
  where open ≡-Reasoning

fromℕ-toℕ : fromℕ ∘ toℕ ≗ id
fromℕ-toℕ = toℕ-injective ∘ toℕ-fromℕ ∘ toℕ

toℕ-inverseˡ : Inverseˡ _≡_ _≡_ toℕ fromℕ
toℕ-inverseˡ = strictlyInverseˡ⇒inverseˡ {f⁻¹ = fromℕ} toℕ toℕ-fromℕ

toℕ-inverseʳ : Inverseʳ _≡_ _≡_ toℕ fromℕ
toℕ-inverseʳ = strictlyInverseʳ⇒inverseʳ toℕ fromℕ-toℕ

toℕ-inverseᵇ : Inverseᵇ _≡_ _≡_ toℕ fromℕ
toℕ-inverseᵇ = toℕ-inverseˡ , toℕ-inverseʳ

fromℕ-pred : ∀ n → fromℕ (ℕ.pred n) ≡ pred (fromℕ n)
fromℕ-pred n = begin
  fromℕ (ℕ.pred n)        ≡⟨ cong (fromℕ ∘ ℕ.pred) (sym (toℕ-fromℕ n)) ⟩
  fromℕ (ℕ.pred (toℕ y))  ≡⟨ cong fromℕ (sym (toℕ-pred y)) ⟩
  fromℕ (toℕ (pred y))    ≡⟨ fromℕ-toℕ (pred y) ⟩
  pred y                  ≡⟨ refl ⟩
  pred (fromℕ n)          ∎
  where open ≡-Reasoning;  y = fromℕ n

x≡0⇒toℕ[x]≡0 : x ≡ zero → toℕ x ≡ 0
x≡0⇒toℕ[x]≡0 {zero} _ = refl

toℕ[x]≡0⇒x≡0 : toℕ x ≡ 0 → x ≡ zero
toℕ[x]≡0⇒x≡0 {zero} _ = refl

------------------------------------------------------------------------
-- Properties of _<_
------------------------------------------------------------------------
-- Basic properties

x≮0 : x ≮ zero
x≮0 ()

x≢0⇒x>0 : x ≢ zero → x > zero
x≢0⇒x>0 {zero}     0≢0 =  contradiction refl 0≢0
x≢0⇒x>0 {2[1+ _ ]} _   =  0<even
x≢0⇒x>0 {1+[2 _ ]} _   =  0<odd

1+[2x]<2[1+x] : ∀ x → 1+[2 x ] < 2[1+ x ]
1+[2x]<2[1+x] x =  odd<even (inj₂ refl)

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ (even<even x<x) refl = <⇒≢ x<x refl
<⇒≢ (odd<odd   x<x) refl = <⇒≢ x<x refl

>⇒≢ : _>_ ⇒ _≢_
>⇒≢ y<x =  ≢-sym (<⇒≢ y<x)

≡⇒≮ : _≡_ ⇒ _≮_
≡⇒≮ x≡y x<y =  <⇒≢ x<y x≡y

≡⇒≯ : _≡_ ⇒ _≯_
≡⇒≯ x≡y x>y =  >⇒≢ x>y x≡y

<⇒≯ : _<_ ⇒ _≯_
<⇒≯ (even<even x<y)        (even<even y<x)        = <⇒≯ x<y y<x
<⇒≯ (even<odd x<y)         (odd<even (inj₁ y<x))  = <⇒≯ x<y y<x
<⇒≯ (even<odd x<y)         (odd<even (inj₂ refl)) = <⇒≢ x<y refl
<⇒≯ (odd<even (inj₁ x<y))  (even<odd y<x)         = <⇒≯ x<y y<x
<⇒≯ (odd<even (inj₂ refl)) (even<odd y<x)         = <⇒≢ y<x refl
<⇒≯ (odd<odd x<y)          (odd<odd y<x)          = <⇒≯ x<y y<x

-- dsp: lemmas
-- dsp: end of lemmas
>⇒≮ : _>_ ⇒ _≮_
>⇒≮ x>y x<z =  <⇒≯ x>y x<z
