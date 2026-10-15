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

>⇒≮ : _>_ ⇒ _≮_
>⇒≮ y<x =  <⇒≯ y<x

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = inj₁

------------------------------------------------------------------------
-- Properties of _<_ and toℕ & fromℕ.

toℕ-mono-< : toℕ Preserves _<_ ⟶ ℕ._<_
toℕ-mono-< {zero}     {2[1+ _ ]} _               =  ℕ.0<1+n
toℕ-mono-< {zero}     {1+[2 _ ]} _               =  ℕ.0<1+n
toℕ-mono-< {2[1+ x ]} {2[1+ y ]} (even<even x<y) =  begin
  ℕ.suc (2 ℕ.* (ℕ.suc xN))    ≤⟨ ℕ.+-monoʳ-≤ 1 (ℕ.*-monoʳ-≤ 2 xN<yN) ⟩
  ℕ.suc (2 ℕ.* yN)            ≤⟨ ℕ.n≤1+n _ ⟩
  2 ℕ.+ (2 ℕ.* yN)            ≡⟨ sym (ℕ.*-distribˡ-+ 2 1 yN) ⟩
  2 ℕ.* (ℕ.suc yN)            ∎
  where open ℕ.≤-Reasoning;  xN = toℕ x;  yN = toℕ y;  xN<yN = toℕ-mono-< x<y
toℕ-mono-< {2[1+ x ]} {1+[2 y ]} (even<odd x<y) =
  ℕ.+-monoʳ-≤ 1 (ℕ.*-monoʳ-≤ 2 (toℕ-mono-< x<y))
toℕ-mono-< {1+[2 x ]} {2[1+ y ]} (odd<even (inj₁ x<y)) =   begin
  ℕ.suc (ℕ.suc (2 ℕ.* xN))    ≡⟨⟩
  2 ℕ.+ (2 ℕ.* xN)            ≡⟨ sym (ℕ.*-distribˡ-+ 2 1 xN) ⟩
  2 ℕ.* (ℕ.suc xN)            ≤⟨ ℕ.*-monoʳ-≤ 2 xN<yN ⟩
  2 ℕ.* yN                    ≤⟨ ℕ.*-monoʳ-≤ 2 (ℕ.n≤1+n _) ⟩
  2 ℕ.* (ℕ.suc yN)            ∎
  where open ℕ.≤-Reasoning;  xN = toℕ x;  yN = toℕ y;  xN<yN = toℕ-mono-< x<y
toℕ-mono-< {1+[2 x ]} {2[1+ .x ]} (odd<even (inj₂ refl)) =
  ℕ.≤-reflexive (sym (ℕ.*-distribˡ-+ 2 1 (toℕ x)))
toℕ-mono-< {1+[2 x ]} {1+[2 y ]} (odd<odd x<y) =  ℕ.+-monoʳ-< 1 (ℕ.*-monoʳ-< 2 xN<yN)
  where xN = toℕ x;  yN = toℕ y;  xN<yN = toℕ-mono-< x<y

toℕ-cancel-< : ∀ {x y} → toℕ x ℕ.< toℕ y → x < y
toℕ-cancel-< {zero}     {2[1+ y ]} x<y = 0<even
toℕ-cancel-< {zero}     {1+[2 y ]} x<y = 0<odd
toℕ-cancel-< {2[1+ x ]} {2[1+ y ]} x<y =
  even<even (toℕ-cancel-< (s<s⁻¹ (ℕ.*-cancelˡ-< 2 _ _ x<y)))
toℕ-cancel-< {2[1+ x ]} {1+[2 y ]} x<y
  rewrite ℕ.*-distribˡ-+ 2 1 (toℕ x) =
  even<odd (toℕ-cancel-< (ℕ.*-cancelˡ-< 2 _ _ (ℕ.≤-trans (s≤s (ℕ.n≤1+n _)) (s<s⁻¹ x<y))))
toℕ-cancel-< {1+[2 x ]} {2[1+ y ]} x<y with toℕ x ℕ.≡? toℕ y
... | yes x≡y = odd<even (inj₂ (toℕ-injective x≡y))
... | no  x≢y
  rewrite ℕ.+-suc (toℕ y) (toℕ y ℕ.+ 0) =
  odd<even (inj₁ (toℕ-cancel-< (ℕ.≤∧≢⇒< (ℕ.*-cancelˡ-≤ 2 (ℕ.+-cancelˡ-≤ 2 _ _ x<y)) x≢y)))
toℕ-cancel-< {1+[2 x ]} {1+[2 y ]} x<y =
  odd<odd (toℕ-cancel-< (ℕ.*-cancelˡ-< 2 _ _ (s<s⁻¹ x<y)))

fromℕ-cancel-< : ∀ {x y} → fromℕ x < fromℕ y → x ℕ.< y
fromℕ-cancel-< = subst₂ ℕ._<_ (toℕ-fromℕ _) (toℕ-fromℕ _) ∘ toℕ-mono-<

fromℕ-mono-< : fromℕ Preserves ℕ._<_ ⟶ _<_
fromℕ-mono-< = toℕ-cancel-< ∘ subst₂ ℕ._<_ (sym (toℕ-fromℕ _)) (sym (toℕ-fromℕ _))

toℕ-isHomomorphism-< : IsOrderHomomorphism _≡_ _≡_ _<_ ℕ._<_ toℕ
toℕ-isHomomorphism-< = record
  { cong = cong toℕ
  ; mono = toℕ-mono-<
  }

toℕ-isMonomorphism-< : IsOrderMonomorphism _≡_ _≡_ _<_ ℕ._<_ toℕ
toℕ-isMonomorphism-< = record
  { isOrderHomomorphism = toℕ-isHomomorphism-<
  ; injective           = toℕ-injective
  ; cancel              = toℕ-cancel-<
  }

------------------------------------------------------------------------
-- Relational properties of _<_

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (even<even x<x) =  <-irrefl refl x<x
<-irrefl refl (odd<odd x<x)   =  <-irrefl refl x<x

<-trans : Transitive _<_
<-trans {zero} {_}      {2[1+ _ ]} _  _        =  0<even
<-trans {zero} {_}      {1+[2 _ ]} _  _        =  0<odd
<-trans (even<even x<y) (even<even y<z)        =  even<even (<-trans x<y y<z)
<-trans (even<even x<y) (even<odd y<z)         =  even<odd (<-trans x<y y<z)
<-trans (even<odd x<y)  (odd<even (inj₁ y<z))  =  even<even (<-trans x<y y<z)
<-trans (even<odd x<y)  (odd<even (inj₂ refl)) =  even<even x<y
<-trans (even<odd x<y)  (odd<odd y<z)          =  even<odd (<-trans x<y y<z)
<-trans (odd<even (inj₁ x<y))  (even<even y<z) =  odd<even (inj₁ (<-trans x<y y<z))
<-trans (odd<even (inj₂ refl)) (even<even x<z) =  odd<even (inj₁ x<z)
<-trans (odd<even (inj₁ x<y))  (even<odd y<z)  =  odd<odd (<-trans x<y y<z)
<-trans (odd<even (inj₂ refl)) (even<odd x<z)  =  odd<odd x<z
<-trans (odd<odd x<y) (odd<even (inj₁ y<z))    =  odd<even (inj₁ (<-trans x<y y<z))
<-trans (odd<odd x<y) (odd<even (inj₂ refl))   =  odd<even (inj₁ x<y)
<-trans (odd<odd x<y) (odd<odd y<z)            =  odd<odd (<-trans x<y y<z)

<-asym : Asymmetric _<_
<-asym {x} {y} = trans∧irr⇒asym refl <-trans <-irrefl {x} {y}

-- Should not be implemented via the morphism `toℕ` in order to
-- preserve O(log n) time requirement.
<-cmp : Trichotomous _≡_ _<_
<-cmp zero     zero      = tri≈ x≮0    refl  x≮0
<-cmp zero     2[1+ _ ]  = tri< 0<even (λ()) x≮0
<-cmp zero     1+[2 _ ]  = tri< 0<odd  (λ()) x≮0
<-cmp 2[1+ _ ] zero      = tri> (λ())  (λ()) 0<even
<-cmp 2[1+ x ] 2[1+ y ]  with <-cmp x y
... | tri< x<y _    _   =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = even<even x<y
... | tri≈ _   refl _   =  tri≈ (<-irrefl refl) refl (<-irrefl refl)
... | tri> _   _    x>y =  tri> (>⇒≮ gt) (>⇒≢ gt) gt  where gt = even<even x>y
<-cmp 2[1+ x ] 1+[2 y ]  with <-cmp x y
... | tri< x<y _    _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = even<odd x<y
... | tri≈ _   refl _ =  tri> (>⇒≮ gt) (>⇒≢ gt) gt
  where
  gt = subst (_< 2[1+ x ]) refl (1+[2x]<2[1+x] x)
... | tri> _ _ y<x =  tri> (>⇒≮ gt) (>⇒≢ gt) gt  where gt = odd<even (inj₁ y<x)
<-cmp 1+[2 _ ] zero =  tri> (>⇒≮ gt) (>⇒≢ gt) gt  where gt = 0<odd
<-cmp 1+[2 x ] 2[1+ y ]  with <-cmp x y
... | tri< x<y _ _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = odd<even (inj₁ x<y)
... | tri≈ _ x≡y _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = odd<even (inj₂ x≡y)
... | tri> _ _ x>y =  tri> (>⇒≮ gt) (>⇒≢ gt) gt  where gt = even<odd x>y
<-cmp 1+[2 x ] 1+[2 y ]  with <-cmp x y
... | tri< x<y _  _   =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = odd<odd x<y
... | tri≈ _ refl _   =  tri≈ (≡⇒≮ refl) refl (≡⇒≯ refl)
... | tri> _ _    x>y =  tri> (>⇒≮ gt) (>⇒≢ gt) gt  where gt = odd<odd x>y

_<?_ : Decidable _<_
_<?_ = tri⇒dec< <-cmp

------------------------------------------------------------------------
-- Structures for _<_

<-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = resp₂ _<_
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  ; compare              = <-cmp
  }

------------------------------------------------------------------------
-- Bundles for _<_

<-strictPartialOrder : StrictPartialOrder _ _ _
<-strictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  }

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = record
  { isStrictTotalOrder =  <-isStrictTotalOrder
  }

------------------------------------------------------------------------
-- Other properties of _<_

x<2[1+x] : ∀ x → x < 2[1+ x ]
x<1+[2x] : ∀ x → x < 1+[2 x ]

x<2[1+x] zero     = 0<even
x<2[1+x] 2[1+ x ] = even<even (x<2[1+x] x)
x<2[1+x] 1+[2 x ] = odd<even (inj₁ (x<1+[2x] x))

x<1+[2x] zero     = 0<odd
x<1+[2x] 2[1+ x ] = even<odd (x<2[1+x] x)
x<1+[2x] 1+[2 x ] = odd<odd (x<1+[2x] x)

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------
-- Basic properties

<⇒≱ : _<_ ⇒ _≱_
<⇒≱ x<y (inj₁ y<x) =  contradiction y<x (<⇒≯ x<y)
<⇒≱ x<y (inj₂ y≡x) =  contradiction (sym y≡x) (<⇒≢ x<y)

≤⇒≯ : _≤_ ⇒ _≯_
≤⇒≯ x≤y x>y =  <⇒≱ x>y x≤y

≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ {x} {y} x≮y  with <-cmp x y
... | tri< lt _  _   =  contradiction lt x≮y
... | tri≈ _  eq _   =  inj₂ (sym eq)
... | tri> _  _  y<x =  <⇒≤ y<x

≰⇒> : _≰_ ⇒ _>_
≰⇒> {x} {y} x≰y  with <-cmp x y
... | tri< lt _  _   =  contradiction (<⇒≤ lt) x≰y
... | tri≈ _  eq _   =  contradiction (inj₂ eq) x≰y
... | tri> _  _  x>y =  x>y

≤∧≢⇒< : ∀ {x y} → x ≤ y → x ≢ y → x < y
≤∧≢⇒< (inj₁ x<y) _   =  x<y
≤∧≢⇒< (inj₂ x≡y) x≢y =  contradiction x≡y x≢y

0≤x : ∀ x → zero ≤ x
0≤x zero     =  inj₂ refl
0≤x 2[1+ _ ] =  inj₁ 0<even
0≤x 1+[2 x ] =  inj₁ 0<odd

x≤0⇒x≡0 : x ≤ zero → x ≡ zero
x≤0⇒x≡0 (inj₂ x≡0) = x≡0

------------------------------------------------------------------------
-- Properties of _<_ and toℕ & fromℕ.

fromℕ-mono-≤ : fromℕ Preserves ℕ._≤_ ⟶ _≤_
fromℕ-mono-≤ m≤n  with ℕ.m≤n⇒m<n∨m≡n m≤n
... | inj₁ m<n =  inj₁ (fromℕ-mono-< m<n)
... | inj₂ m≡n =  inj₂ (cong fromℕ m≡n)

toℕ-mono-≤ : toℕ Preserves _≤_ ⟶ ℕ._≤_
toℕ-mono-≤ (inj₁ x<y)  =  ℕ.<⇒≤ (toℕ-mono-< x<y)
toℕ-mono-≤ (inj₂ refl) =  ℕ.≤-reflexive refl

toℕ-cancel-≤ : ∀ {x y} → toℕ x ℕ.≤ toℕ y → x ≤ y
toℕ-cancel-≤ = subst₂ _≤_ (fromℕ-toℕ _) (fromℕ-toℕ _) ∘ fromℕ-mono-≤

fromℕ-cancel-≤ : ∀ {x y} → fromℕ x ≤ fromℕ y → x ℕ.≤ y
fromℕ-cancel-≤ = subst₂ ℕ._≤_ (toℕ-fromℕ _) (toℕ-fromℕ _) ∘ toℕ-mono-≤

toℕ-isHomomorphism-≤ : IsOrderHomomorphism _≡_ _≡_ _≤_ ℕ._≤_ toℕ
toℕ-isHomomorphism-≤ = record
  { cong = cong toℕ
  ; mono = toℕ-mono-≤
  }

toℕ-isMonomorphism-≤ : IsOrderMonomorphism _≡_ _≡_ _≤_ ℕ._≤_ toℕ
toℕ-isMonomorphism-≤ = record
  { isOrderHomomorphism = toℕ-isHomomorphism-≤
  ; injective           = toℕ-injective
  ; cancel              = toℕ-cancel-≤
  }

------------------------------------------------------------------------
-- Relational properties of _≤_

≤-refl : Reflexive _≤_
≤-refl =  inj₂ refl

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive {x} {_} refl =  ≤-refl {x}

≤-trans : Transitive _≤_
≤-trans = StrictToNonStrict.trans isEquivalence (resp₂ _<_) <-trans

<-≤-trans : ∀ {x y z} → x < y → y ≤ z → x < z
<-≤-trans x<y (inj₁ y<z)  =  <-trans x<y y<z
<-≤-trans x<y (inj₂ refl) =  x<y

≤-<-trans : ∀ {x y z} → x ≤ y → y < z → x < z
≤-<-trans (inj₁ x<y)  y<z =  <-trans x<y y<z
≤-<-trans (inj₂ refl) y<z =  y<z

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym = StrictToNonStrict.antisym isEquivalence <-trans <-irrefl

≤-total : Total _≤_
≤-total x y with <-cmp x y
... | tri< x<y _  _   = inj₁ (<⇒≤ x<y)
... | tri≈ _  x≡y _   = inj₁ (≤-reflexive x≡y)
... | tri> _  _   y<x = inj₂ (<⇒≤ y<x)

-- Should not be implemented via the morphism `toℕ` in order to
-- preserve O(log n) time requirement.
_≤?_ : Decidable _≤_
x ≤? y with <-cmp x y
... | tri< x<y _   _   = yes (<⇒≤ x<y)
... | tri≈ _   x≡y _   = yes (≤-reflexive x≡y)
... | tri> _   _   y<x = no (<⇒≱ y<x)


------------------------------------------------------------------------
-- Structures

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≈?_         = _≡?_
  ; _≤?_         = _≤?_
  }

------------------------------------------------------------------------
-- Bundles

≤-preorder : Preorder 0ℓ 0ℓ 0ℓ
≤-preorder = record
  { isPreorder = ≤-isPreorder
  }

≤-partialOrder : Poset 0ℓ 0ℓ 0ℓ
≤-partialOrder = record
  { isPartialOrder = ≤-isPartialOrder
  }

≤-totalOrder : TotalOrder 0ℓ 0ℓ 0ℓ
≤-totalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  }

≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }

------------------------------------------------------------------------
-- Equational reasoning for _≤_ and _<_

module ≤-Reasoning where

  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-asym
    <-trans
    (resp₂ _<_)
    <⇒≤
    <-≤-trans
    ≤-<-trans
    public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)

------------------------------------------------------------------------
-- Properties of _<ℕ_
------------------------------------------------------------------------

<⇒<ℕ : ∀ {x y} → x < y → x <ℕ y
<⇒<ℕ x<y = toℕ-mono-< x<y

<ℕ⇒< : ∀ {x y} → x <ℕ y → x < y
<ℕ⇒< {x} {y} t[x]<t[y] = begin-strict
  x             ≡⟨ sym (fromℕ-toℕ x) ⟩
  fromℕ (toℕ x) <⟨ fromℕ-mono-< t[x]<t[y] ⟩
  fromℕ (toℕ y) ≡⟨ fromℕ-toℕ y ⟩
  y             ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _+_

-- toℕ/fromℕ are homomorphisms for _+_

toℕ-homo-+ : ∀ x y → toℕ (x + y) ≡ toℕ x ℕ.+ toℕ y
toℕ-homo-+ zero     _        = refl
toℕ-homo-+ 2[1+ x ] zero     = cong ℕ.suc (sym (ℕ.+-identityʳ _))
toℕ-homo-+ 1+[2 x ] zero     = cong ℕ.suc (sym (ℕ.+-identityʳ _))
toℕ-homo-+ 2[1+ x ] 2[1+ y ] = begin
  toℕ (2[1+ x ] + 2[1+ y ])          ≡⟨⟩
  toℕ 2[1+ (suc (x + y)) ]           ≡⟨⟩
  2 ℕ.* (1 ℕ.+ (toℕ (suc (x + y))))  ≡⟨ cong ((2 ℕ.*_) ∘ ℕ.suc) (toℕ-suc (x + y)) ⟩
  2 ℕ.* (2 ℕ.+ toℕ (x + y))          ≡⟨ cong ((2 ℕ.*_) ∘ (2 ℕ.+_)) (toℕ-homo-+ x y) ⟩
  2 ℕ.* (2 ℕ.+ (toℕ x ℕ.+ toℕ y))    ≡⟨ solve 2 (λ m n → con 2 :* (con 2 :+ (m :+ n))  :=
                                          con 2 :* (con 1 :+ m) :+ con 2 :* (con 1 :+ n))
                                          refl (toℕ x) (toℕ y) ⟩
  toℕ 2[1+ x ] ℕ.+ toℕ 2[1+ y ]      ∎
  where open ≡-Reasoning

toℕ-homo-+ 2[1+ x ] 1+[2 y ] = begin
  toℕ (2[1+ x ] + 1+[2 y ])             ≡⟨⟩
  toℕ (suc 2[1+ (x + y) ])              ≡⟨ toℕ-suc 2[1+ (x + y) ] ⟩
  ℕ.suc (toℕ 2[1+ (x + y) ])            ≡⟨⟩
  ℕ.suc (2 ℕ.* (ℕ.suc (toℕ (x + y))))   ≡⟨ cong (λ v → ℕ.suc (2 ℕ.* ℕ.suc v)) (toℕ-homo-+ x y) ⟩
  ℕ.suc (2 ℕ.* (ℕ.suc (m ℕ.+ n)))       ≡⟨ solve 2 (λ m n → con 1 :+ (con 2 :* (con 1 :+ (m :+ n))) :=
                                             con 2 :* (con 1 :+ m) :+ (con 1 :+ (con 2 :* n)))
                                             refl m n ⟩
  (2 ℕ.* ℕ.suc m) ℕ.+ (ℕ.suc (2 ℕ.* n)) ≡⟨⟩
  toℕ 2[1+ x ] ℕ.+ toℕ 1+[2 y ]         ∎
  where open ≡-Reasoning;  m = toℕ x; n = toℕ y

toℕ-homo-+ 1+[2 x ] 2[1+ y ] = begin
  toℕ (1+[2 x ] + 2[1+ y ])                 ≡⟨⟩
  toℕ (suc 2[1+ (x + y) ])                  ≡⟨ toℕ-suc 2[1+ (x + y) ] ⟩
  ℕ.suc (toℕ 2[1+ (x + y) ])                ≡⟨⟩
  ℕ.suc (2 ℕ.* (ℕ.suc (toℕ (x + y))))       ≡⟨ cong (ℕ.suc ∘ (2 ℕ.*_) ∘ ℕ.suc) (toℕ-homo-+ x y) ⟩
  ℕ.suc (2 ℕ.* (ℕ.suc (m ℕ.+ n)))           ≡⟨ solve 2 (λ m n → con 1 :+ (con 2 :* (con 1 :+ (m :+ n))) :=
                                                 (con 1 :+ (con 2 :* m)) :+ (con 2 :* (con 1 :+ n)))
                                                 refl m n ⟩
  (ℕ.suc (2 ℕ.* m)) ℕ.+ (2 ℕ.* (ℕ.suc n))   ≡⟨⟩
  toℕ 1+[2 x ] ℕ.+ toℕ 2[1+ y ]             ∎
  where open ≡-Reasoning;  m = toℕ x;  n = toℕ y

toℕ-homo-+ 1+[2 x ] 1+[2 y ] = begin
  toℕ (1+[2 x ] + 1+[2 y ])               ≡⟨⟩
  toℕ (suc 1+[2 (x + y) ])                ≡⟨ toℕ-suc 1+[2 (x + y) ] ⟩
  ℕ.suc (toℕ 1+[2 (x + y) ])              ≡⟨⟩
  ℕ.suc (ℕ.suc (2 ℕ.* (toℕ (x + y))))     ≡⟨ cong (ℕ.suc ∘ ℕ.suc ∘ (2 ℕ.*_)) (toℕ-homo-+ x y) ⟩
  ℕ.suc (ℕ.suc (2 ℕ.* (m ℕ.+ n)))         ≡⟨ solve 2 (λ m n → con 1 :+ (con 1 :+ (con 2 :* (m :+ n))) :=
                                               (con 1 :+ (con 2 :* m)) :+ (con 1 :+ (con 2 :* n)))
                                               refl m n ⟩
  (ℕ.suc (2 ℕ.* m)) ℕ.+ (ℕ.suc (2 ℕ.* n)) ≡⟨⟩
  toℕ 1+[2 x ] ℕ.+ toℕ 1+[2 y ]           ∎
  where open ≡-Reasoning;  m = toℕ x;  n = toℕ y

toℕ-isMagmaHomomorphism-+ : IsMagmaHomomorphism +-rawMagma ℕ.+-rawMagma toℕ
toℕ-isMagmaHomomorphism-+ = record
  { isRelHomomorphism = toℕ-isRelHomomorphism
  ; ∙-homo            = toℕ-homo-+
  }

toℕ-isMonoidHomomorphism-+ : IsMonoidHomomorphism +-0-rawMonoid ℕ.+-0-rawMonoid toℕ
toℕ-isMonoidHomomorphism-+ = record
  { isMagmaHomomorphism = toℕ-isMagmaHomomorphism-+
  ; ε-homo              = refl
  }

toℕ-isMonoidMonomorphism-+ : IsMonoidMonomorphism +-0-rawMonoid ℕ.+-0-rawMonoid toℕ
toℕ-isMonoidMonomorphism-+ = record
  { isMonoidHomomorphism = toℕ-isMonoidHomomorphism-+
  ; injective            = toℕ-injective
  }

suc≗1+ : suc ≗ 1ᵇ +_
suc≗1+ zero     = refl
suc≗1+ 2[1+ _ ] = refl
suc≗1+ 1+[2 _ ] = refl

suc-+ : ∀ x y → suc x + y ≡ suc (x + y)
suc-+ zero        y     =  sym (suc≗1+ y)
suc-+ 2[1+ x ] zero     =  refl
suc-+ 1+[2 x ] zero     =  refl
suc-+ 2[1+ x ] 2[1+ y ] =  cong (suc ∘ 2[1+_]) (suc-+ x y)
suc-+ 2[1+ x ] 1+[2 y ] =  cong (suc ∘ 1+[2_]) (suc-+ x y)
suc-+ 1+[2 x ] 2[1+ y ] =  refl
suc-+ 1+[2 x ] 1+[2 y ] =  refl

1+≗suc : (1ᵇ +_) ≗ suc
1+≗suc = suc-+ zero

fromℕ'-homo-+ : ∀ m n → fromℕ' (m ℕ.+ n) ≡ fromℕ' m + fromℕ' n
fromℕ'-homo-+ 0         _ = refl
fromℕ'-homo-+ (ℕ.suc m) n = begin
  fromℕ' ((ℕ.suc m) ℕ.+ n)         ≡⟨⟩
  suc (fromℕ' (m ℕ.+ n))           ≡⟨ cong suc (fromℕ'-homo-+ m n) ⟩
  suc (a + b)                      ≡⟨ sym (suc-+ a b) ⟩
  (suc a) + b                      ≡⟨⟩
  (fromℕ' (ℕ.suc m)) + (fromℕ' n)  ∎
  where open ≡-Reasoning;  a = fromℕ' m;  b = fromℕ' n

fromℕ-homo-+ : ∀ m n → fromℕ (m ℕ.+ n) ≡ fromℕ m + fromℕ n
fromℕ-homo-+ m n rewrite fromℕ≡fromℕ' (m ℕ.+ n) | fromℕ≡fromℕ' m | fromℕ≡fromℕ' n =
  fromℕ'-homo-+ m n

------------------------------------------------------------------------
-- Algebraic properties of _+_

-- Mostly proved by using the isomorphism between `ℕ` and `ℕᵇ` provided
-- by `toℕ`/`fromℕ`.

private
  module +-Monomorphism = MonoidMonomorphism toℕ-isMonoidMonomorphism-+

+-assoc : Associative _+_
+-assoc = +-Monomorphism.assoc ℕ.+-isMagma ℕ.+-assoc

+-comm : Commutative _+_
+-comm = +-Monomorphism.comm ℕ.+-isMagma ℕ.+-comm

+-identityˡ : LeftIdentity zero _+_
+-identityˡ _ = refl

+-identityʳ : RightIdentity zero _+_
+-identityʳ = +-Monomorphism.identityʳ ℕ.+-isMagma ℕ.+-identityʳ

+-identity : Identity zero _+_
+-identity = +-identityˡ , +-identityʳ

+-cancelˡ-≡ : LeftCancellative _+_
+-cancelˡ-≡ = +-Monomorphism.cancelˡ ℕ.+-isMagma ℕ.+-cancelˡ-≡

+-cancelʳ-≡ : RightCancellative _+_
+-cancelʳ-≡ = +-Monomorphism.cancelʳ ℕ.+-isMagma ℕ.+-cancelʳ-≡

------------------------------------------------------------------------
-- Structures for _+_

+-isMagma : IsMagma _+_
+-isMagma = isMagma _+_

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = +-Monomorphism.isSemigroup ℕ.+-isSemigroup

+-isCommutativeSemigroup : IsCommutativeSemigroup _+_
+-isCommutativeSemigroup = record
  { isSemigroup = +-isSemigroup
  ; comm        = +-comm
  }

+-0-isMonoid : IsMonoid _+_ 0ᵇ
+-0-isMonoid = +-Monomorphism.isMonoid ℕ.+-0-isMonoid

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ 0ᵇ
+-0-isCommutativeMonoid = +-Monomorphism.isCommutativeMonoid ℕ.+-0-isCommutativeMonoid

------------------------------------------------------------------------
-- Bundles for _+_

+-magma : Magma 0ℓ 0ℓ
+-magma = magma _+_

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
+-commutativeSemigroup = record
  { isCommutativeSemigroup = +-isCommutativeSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { ε        = zero
  ; isMonoid = +-0-isMonoid
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

module Bin+CSemigroup = CommSemigProp +-commutativeSemigroup

------------------------------------------------------------------------
-- Properties of _+_ and _≤_

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {x} {x′} {y} {y′} x≤x′ y≤y′ =  begin
  x + y                 ≡⟨ sym $ cong₂ _+_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m + fromℕ n     ≡⟨ sym (fromℕ-homo-+ m n) ⟩
  fromℕ (m ℕ.+ n)       ≤⟨ fromℕ-mono-≤ (ℕ.+-mono-≤ m≤m′ n≤n′) ⟩
  fromℕ (m′ ℕ.+ n′)     ≡⟨ fromℕ-homo-+ m′ n′ ⟩
  fromℕ m′ + fromℕ n′   ≡⟨ cong₂ _+_ (fromℕ-toℕ x′) (fromℕ-toℕ y′) ⟩
  x′ + y′               ∎
  where
  open ≤-Reasoning
  m    = toℕ x;             m′   = toℕ x′
  n    = toℕ y;             n′   = toℕ y′
  m≤m′ = toℕ-mono-≤ x≤x′;   n≤n′ = toℕ-mono-≤ y≤y′

+-monoˡ-≤ : ∀ x → (_+ x) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ x y≤z =  +-mono-≤ y≤z (≤-refl {x})

+-monoʳ-≤ : ∀ x → (x +_) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ x y≤z =  +-mono-≤ (≤-refl {x}) y≤z

+-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {x} {x′} {y} {y′} x<x′ y≤y′ =  begin-strict
  x + y                  ≡⟨ sym $ cong₂ _+_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m + fromℕ n      ≡⟨ sym (fromℕ-homo-+ m n) ⟩
  fromℕ (m ℕ.+ n)        <⟨ fromℕ-mono-< (ℕ.+-mono-<-≤ m<m′ n≤n′) ⟩
  fromℕ (m′ ℕ.+ n′)      ≡⟨ fromℕ-homo-+ m′ n′ ⟩
  fromℕ m′ + fromℕ n′    ≡⟨ cong₂ _+_ (fromℕ-toℕ x′) (fromℕ-toℕ y′) ⟩
  x′ + y′                ∎
  where
  open ≤-Reasoning
  m    = toℕ x;             n    = toℕ y
  m′   = toℕ x′;            n′   = toℕ y′
  m<m′ = toℕ-mono-< x<x′;   n≤n′ = toℕ-mono-≤ y≤y′

+-mono-≤-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {x} {x′} {y} {y′} x≤x′ y<y′ =  subst₂ _<_ (+-comm y x) (+-comm y′ x′) y+x<y′+x′
  where
  y+x<y′+x′ =  +-mono-<-≤ y<y′ x≤x′

-- dsp: lemmas
-- dsp: end of lemmas
+-monoˡ-< : ∀ x → (_+ x) Preserves _<_ ⟶ _<_
+-monoˡ-< x {y} {z} y<z = begin-strict
  y + x            ≡⟨ {!!} ⟩
  fromℕ t + fromℕ s ≡⟨ {!!} ⟩
  fromℕ t + fromℕ s <⟨ {!!} ⟩
  suc (fromℕ t) + x ≡⟨ {!!} ⟩
  z + x            ∎ where open ≤-Reasoning;  t = toℕ y; s = toℕ x
