------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutations using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Relation.Binary.Core
  using (Rel; _⇒_; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions as B hiding (Decidable)

module Data.List.Relation.Binary.Permutation.Setoid.Properties
  {a ℓ} (S : Setoid a ℓ)
  where

open import Algebra
open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (zero; suc)
open import Data.List.Base as List hiding (head; tail)
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; head; tail)
import Data.List.Relation.Binary.Equality.Setoid as Equality
import Data.List.Relation.Binary.Permutation.Setoid as Permutation
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.Unique.Setoid as Unique
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties using (∈-∃++; ∈-insert)
import Data.List.Properties as List
open import Data.Nat.Base using (ℕ; suc; 2+; _<_; z<s; _+_)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Product.Base using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Function.Base using (_∘_; _⟨_⟩_; flip)
open import Function.Bundles using (Inverse)
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred; Decidable)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Properties.Setoid S using (≉-resp₂)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_ ; refl; sym; cong; cong₂; subst; _≢_)
open import Relation.Nullary.Decidable using (yes; no; does)
open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)


open Setoid S using (_≈_)
  renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open Permutation S
open Membership S
open Unique S using (Unique)
open module ≋ = Equality S
  using (_≋_; []; _∷_
        ; ≋-refl; ≋-sym; ≋-trans
        ; All-resp-≋; Any-resp-≋; AllPairs-resp-≋)

private
  variable
    b p r : Level
    x y z v w : A
    xs ys zs vs ws : List A
    P : Pred A p
    R : Rel A r


------------------------------------------------------------------------
-- Relationships to other predicates
------------------------------------------------------------------------

All-resp-↭ : P Respects _≈_ → (All P) Respects _↭_
All-resp-↭ resp (refl xs≋ys)   pxs             = All-resp-≋ resp xs≋ys pxs
All-resp-↭ resp (prep x≈y p)   (px ∷ pxs)      = resp x≈y px ∷ All-resp-↭ resp p pxs
All-resp-↭ resp (swap ≈₁ ≈₂ p) (px ∷ py ∷ pxs) = resp ≈₂ py ∷ resp ≈₁ px ∷ All-resp-↭ resp p pxs
All-resp-↭ resp (trans p₁ p₂)  pxs             = All-resp-↭ resp p₂ (All-resp-↭ resp p₁ pxs)

Any-resp-↭ : P Respects _≈_ → (Any P) Respects _↭_
Any-resp-↭ resp (refl xs≋ys) pxs                 = Any-resp-≋ resp xs≋ys pxs
Any-resp-↭ resp (prep x≈y p) (here px)           = here (resp x≈y px)
Any-resp-↭ resp (prep x≈y p) (there pxs)         = there (Any-resp-↭ resp p pxs)
Any-resp-↭ resp (swap x y p) (here px)           = there (here (resp x px))
Any-resp-↭ resp (swap x y p) (there (here px))   = here (resp y px)
Any-resp-↭ resp (swap x y p) (there (there pxs)) = there (there (Any-resp-↭ resp p pxs))
Any-resp-↭ resp (trans p₁ p₂) pxs                = Any-resp-↭ resp p₂ (Any-resp-↭ resp p₁ pxs)

AllPairs-resp-↭ : Symmetric R → R Respects₂ _≈_ → (AllPairs R) Respects _↭_
AllPairs-resp-↭ sym resp (refl xs≋ys)     pxs             = AllPairs-resp-≋ resp xs≋ys pxs
AllPairs-resp-↭ sym resp (prep x≈y p)     (∼ ∷ pxs)       =
  All-resp-↭ (proj₁ resp) p (All.map (proj₂ resp x≈y) ∼) ∷
  AllPairs-resp-↭ sym resp p pxs
AllPairs-resp-↭ sym resp@(rʳ , rˡ) (swap eq₁ eq₂ p) ((∼₁ ∷ ∼₂) ∷ ∼₃ ∷ pxs) =
  (sym (rʳ eq₂ (rˡ eq₁ ∼₁)) ∷ All-resp-↭ rʳ p (All.map (rˡ eq₂) ∼₃)) ∷
  All-resp-↭ rʳ p (All.map (rˡ eq₁) ∼₂) ∷
  AllPairs-resp-↭ sym resp p pxs
AllPairs-resp-↭ sym resp (trans p₁ p₂)    pxs             =
  AllPairs-resp-↭ sym resp p₂ (AllPairs-resp-↭ sym resp p₁ pxs)

∈-resp-↭ : (x ∈_) Respects _↭_
∈-resp-↭ = Any-resp-↭ (flip ≈-trans)

Unique-resp-↭ : Unique Respects _↭_
Unique-resp-↭ = AllPairs-resp-↭ (_∘ ≈-sym) ≉-resp₂

------------------------------------------------------------------------
-- Length

xs↭ys⇒|xs|≡|ys| : ∀ {xs ys} → xs ↭ ys → length xs ≡ length ys
xs↭ys⇒|xs|≡|ys| (refl eq)            = Pointwise.Pointwise-length eq
xs↭ys⇒|xs|≡|ys| (prep eq xs↭ys)      = ≡.cong suc (xs↭ys⇒|xs|≡|ys| xs↭ys)
xs↭ys⇒|xs|≡|ys| (swap eq₁ eq₂ xs↭ys) = ≡.cong 2+ (xs↭ys⇒|xs|≡|ys| xs↭ys)
xs↭ys⇒|xs|≡|ys| (trans xs↭ys xs↭ys₁) = ≡.trans (xs↭ys⇒|xs|≡|ys| xs↭ys) (xs↭ys⇒|xs|≡|ys| xs↭ys₁)

¬x∷xs↭[] : ∀ {x xs} → ¬ (x ∷ xs ↭ [])
¬x∷xs↭[] = contraposition xs↭ys⇒|xs|≡|ys| λ()

------------------------------------------------------------------------
-- Core properties depending on the representation of _↭_
------------------------------------------------------------------------

shift : v ≈ w → ∀ xs ys → xs ++ [ v ] ++ ys ↭ w ∷ xs ++ ys
shift {v} {w} v≈w []       ys = prep v≈w ↭-refl
shift {v} {w} v≈w (x ∷ xs) ys = begin
  x ∷ (xs ++ [ v ] ++ ys) ↭⟨ ↭-prep x (shift v≈w xs ys) ⟩
  x ∷ w ∷ xs ++ ys        ↭⟨ ↭-swap x w ↭-refl ⟩
  w ∷ x ∷ xs ++ ys        ∎
  where open PermutationReasoning

------------------------------------------------------------------------
-- Relationship to `_≋_`
------------------------------------------------------------------------

↭-split : ∀ v as bs → xs ↭ (as ++ [ v ] ++ bs) →
          ∃₂ λ ps qs → xs ≋ (ps ++ [ v ] ++ qs)
                     × (ps ++ qs) ↭ (as ++ bs)
↭-split v as bs p = helper as bs p ≋-refl
  where
  helper : ∀ as bs → xs ↭ ys → ys ≋ (as ++ [ v ] ++ bs) →
           ∃₂ λ ps qs → xs ≋ (ps ++ [ v ] ++ qs)
                      × (ps ++ qs) ↭ (as ++ bs)
  helper as           bs (trans xs↭ys ys↭zs) zs≋as++[v]++ys
    with ps , qs , eq , ↭ ← helper as bs ys↭zs zs≋as++[v]++ys
    with ps′ , qs′ , eq′ , ↭′ ← helper ps qs xs↭ys eq
    = ps′ , qs′ , eq′ , ↭-trans′ ↭′ ↭
  helper []           _  (refl (x≈v ∷ xs≋vs)) (v≈y ∷ vs≋ys)
    = [] , _ , ≈-trans x≈v v≈y ∷ ≋-refl , refl (≋-trans xs≋vs vs≋ys)
  helper (a ∷ as)     bs (refl (x≈v ∷ xs≋vs)) (v≈y ∷ vs≋ys)
    = _ ∷ as , bs , ≈-trans x≈v v≈y ∷ ≋-trans xs≋vs vs≋ys , ↭-refl
  helper []           bs (prep {xs = xs} x≈v xs↭vs) (v≈y ∷ vs≋ys)
    = [] , xs , ≈-trans x≈v v≈y ∷ ≋-refl , ↭-transʳ-≋ xs↭vs vs≋ys
  helper (a ∷ as)     bs (prep x≈v as↭vs) (v≈y ∷ vs≋ys)
    with ps , qs , eq , ↭ ← helper as bs as↭vs vs≋ys
    = a ∷ ps , qs , ≈-trans x≈v v≈y ∷ eq , prep ≈-refl ↭
  helper []           [] (swap _ _ _) (_ ∷ ())
  helper []      (b ∷ _) (swap x≈v y≈w xs↭vs) (w≈z ∷ v≈y ∷ vs≋ys)
    = b ∷ [] , _ , ≈-trans x≈v v≈y ∷ ≈-trans y≈w w≈z ∷ ≋-refl
                 , ↭-prep b (↭-transʳ-≋ xs↭vs vs≋ys)
  helper (a ∷ [])     bs (swap x≈v y≈w xs↭vs)  (w≈z ∷ v≈y ∷ vs≋ys)
    = []     , a ∷ _ , ≈-trans x≈v v≈y ∷ ≈-trans y≈w w≈z ∷ ≋-refl
                     , ↭-prep a (↭-transʳ-≋ xs↭vs vs≋ys)
  helper (a ∷ b ∷ as) bs (swap x≈v y≈w as↭vs) (w≈a ∷ v≈b ∷ vs≋ys)
    with ps , qs , eq , ↭ ← helper as bs as↭vs vs≋ys
    = b ∷ a ∷ ps , qs , ≈-trans x≈v v≈b ∷ ≈-trans y≈w w≈a ∷ eq
                      , ↭-swap _ _ ↭

------------------------------------------------------------------------
-- Core properties of lists depending on the representation of _↭_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- map

module _ (T : Setoid b r) where

  open Setoid T using () renaming (_≈_ to _≈′_)
  open Permutation T using () renaming (_↭_ to _↭′_)

  map⁺ : ∀ {f} → f Preserves _≈_ ⟶ _≈′_ → (map f) Preserves _↭_ ⟶ _↭′_
  map⁺ pres (refl xs≋ys)  = refl (Pointwise.map⁺ _ _ (Pointwise.map pres xs≋ys))
  map⁺ pres (prep x p)    = prep (pres x) (map⁺ pres p)
  map⁺ pres (swap x y p)  = swap (pres x) (pres y) (map⁺ pres p)
  map⁺ pres (trans p₁ p₂) = trans (map⁺ pres p₁) (map⁺ pres p₂)

------------------------------------------------------------------------
-- filter

module _ (P? : Decidable P) (P≈ : P Respects _≈_) where

  filter⁺ : ∀ {xs ys : List A} → xs ↭ ys → filter P? xs ↭ filter P? ys
  filter⁺ (refl xs≋ys)        = refl (≋.filter⁺ P? P≈ xs≋ys)
  filter⁺ (trans xs↭zs zs↭ys) = trans (filter⁺ xs↭zs) (filter⁺ zs↭ys)
  filter⁺ {x ∷ xs} {y ∷ ys} (prep x≈y xs↭ys) with P? x | P? y
  ... | yes _  | yes _  = prep x≈y (filter⁺ xs↭ys)
  ... | yes Px | no ¬Py = contradiction (P≈ x≈y Px) ¬Py
  ... | no ¬Px | yes Py = contradiction (P≈ (≈-sym x≈y) Py) ¬Px
  ... | no  _  | no  _  = filter⁺ xs↭ys
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) with P? x | P? y
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) | no ¬Px | no ¬Py
    with P? z | P? w
  ... | _      | yes Pw = contradiction (P≈ w≈y Pw) ¬Py
  ... | yes Pz | _      = contradiction (P≈ (≈-sym x≈z) Pz) ¬Px
  ... | no _   | no  _  = filter⁺ xs↭ys
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) | no ¬Px | yes Py
    with P? z | P? w
  ... | _      | no ¬Pw = contradiction (P≈ (≈-sym w≈y) Py) ¬Pw
  ... | yes Pz | _      = contradiction (P≈ (≈-sym x≈z) Pz) ¬Px
  ... | no _   | yes _  = prep w≈y (filter⁺ xs↭ys)
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys)  | yes Px | no ¬Py
    with P? z | P? w
  ... | no ¬Pz | _      = contradiction (P≈ x≈z Px) ¬Pz
  ... | _      | yes Pw = contradiction (P≈ w≈y Pw) ¬Py
  ... | yes _  | no _   = prep x≈z (filter⁺ xs↭ys)
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) | yes Px | yes Py
    with P? z | P? w
  ... | no ¬Pz | _      = contradiction (P≈ x≈z Px) ¬Pz
  ... | _      | no ¬Pw = contradiction (P≈ (≈-sym w≈y) Py) ¬Pw
  ... | yes _  | yes _  = swap x≈z w≈y (filter⁺ xs↭ys)

------------------------------------------------------------------------
-- _++_

++⁺ʳ : ∀ zs → xs ↭ ys → xs ++ zs ↭ ys ++ zs
++⁺ʳ zs (refl xs≋ys)  = refl (Pointwise.++⁺ xs≋ys ≋-refl)
++⁺ʳ zs (prep x ↭)    = prep x (++⁺ʳ zs ↭)
++⁺ʳ zs (swap x y ↭)  = swap x y (++⁺ʳ zs ↭)
++⁺ʳ zs (trans ↭₁ ↭₂) = trans (++⁺ʳ zs ↭₁) (++⁺ʳ zs ↭₂)

------------------------------------------------------------------------
-- dropMiddleElement-≋

dropMiddleElement-≋ : ∀ {x} ws xs {ys} {zs} →
           ws ++ [ x ] ++ ys ≋ xs ++ [ x ] ++ zs →
           ws ++ ys ↭ xs ++ zs
dropMiddleElement-≋ []       []       (_   ∷ eq) = ↭-reflexive-≋ eq
dropMiddleElement-≋ []       (x ∷ xs) (w≈v ∷ eq) = ↭-transˡ-≋ eq (shift w≈v xs _)
dropMiddleElement-≋ (w ∷ ws) []       (w≈x ∷ eq) = ↭-transʳ-≋ (↭-sym (shift (≈-sym w≈x) ws _)) eq
dropMiddleElement-≋ (w ∷ ws) (x ∷ xs) (w≈x ∷ eq) = prep w≈x (dropMiddleElement-≋ ws xs eq)

------------------------------------------------------------------------
-- Properties depending on the core properties of _↭_
------------------------------------------------------------------------

↭-shift : ∀ {v} xs ys → xs ++ [ v ] ++ ys ↭ v ∷ xs ++ ys
↭-shift = shift ≈-refl

++⁺ˡ : ∀ xs {ys zs} → ys ↭ zs → xs ++ ys ↭ xs ++ zs
++⁺ˡ []       ys↭zs = ys↭zs
++⁺ˡ (x ∷ xs) ys↭zs = ↭-prep _ (++⁺ˡ xs ys↭zs)

++⁺ : _++_ Preserves₂ _↭_ ⟶ _↭_ ⟶ _↭_
++⁺ ws↭xs ys↭zs = ↭-trans (++⁺ʳ _ ws↭xs) (++⁺ˡ _ ys↭zs)

-- Some other useful lemmas

zoom : ∀ h {t xs ys} → xs ↭ ys → h ++ xs ++ t ↭ h ++ ys ++ t
zoom h {t} = ++⁺ˡ h ∘ ++⁺ʳ t

inject : ∀ v {ws xs ys zs} → ws ↭ ys → xs ↭ zs →
         ws ++ [ v ] ++ xs ↭ ys ++ [ v ] ++ zs
inject v ws↭ys xs↭zs = ↭-trans (++⁺ˡ _ (↭-prep _ xs↭zs)) (++⁺ʳ _ ws↭ys)

-- Algebraic properties

++-identityˡ : LeftIdentity _↭_ [] _++_
++-identityˡ xs = ↭-refl

++-identityʳ : RightIdentity _↭_ [] _++_
++-identityʳ xs = ↭-reflexive (List.++-identityʳ xs)

++-identity : Identity _↭_ [] _++_
++-identity = ++-identityˡ , ++-identityʳ

++-assoc : Associative _↭_ _++_
++-assoc xs ys zs = ↭-reflexive (List.++-assoc xs ys zs)

++-comm : Commutative _↭_ _++_
++-comm []       ys = ↭-sym (++-identityʳ ys)
++-comm (x ∷ xs) ys = begin
  x ∷ xs ++ ys   ↭⟨ ↭-prep x (++-comm xs ys) ⟩
  x ∷ ys ++ xs   ↭⟨ ↭-shift ys xs ⟨
  ys ++ (x ∷ xs) ∎
  where open PermutationReasoning

-- Corollary

shifts : ∀ xs ys {zs} → xs ++ ys ++ zs ↭ ys ++ xs ++ zs
shifts xs ys {zs} = begin
   xs ++ ys  ++ zs ↭⟨ ++-assoc xs ys zs ⟨
  (xs ++ ys) ++ zs ↭⟨ ++⁺ʳ zs (++-comm xs ys) ⟩
  (ys ++ xs) ++ zs ↭⟨ ++-assoc ys xs zs ⟩
   ys ++ xs  ++ zs ∎
  where open PermutationReasoning

-- Structures

++-isMagma : IsMagma _↭_ _++_
++-isMagma = record
  { isEquivalence = ↭-isEquivalence
  ; ∙-cong        = ++⁺
  }

++-isSemigroup : IsSemigroup _↭_ _++_
++-isSemigroup = record
  { isMagma = ++-isMagma
  ; assoc   = ++-assoc
  }

++-isMonoid : IsMonoid _↭_ _++_ []
++-isMonoid = record
  { isSemigroup = ++-isSemigroup
  ; identity    = ++-identity
  }

++-isCommutativeMonoid : IsCommutativeMonoid _↭_ _++_ []
++-isCommutativeMonoid = record
  { isMonoid = ++-isMonoid
  ; comm     = ++-comm
  }

-- Bundles

++-magma : Magma a (a ⊔ ℓ)
++-magma = record
  { isMagma = ++-isMagma
  }

++-semigroup : Semigroup a (a ⊔ ℓ)
++-semigroup = record
  { isSemigroup = ++-isSemigroup
  }

++-monoid : Monoid a (a ⊔ ℓ)
++-monoid = record
  { isMonoid = ++-isMonoid
  }

++-commutativeMonoid : CommutativeMonoid a (a ⊔ ℓ)
++-commutativeMonoid = record
  { isCommutativeMonoid = ++-isCommutativeMonoid
  }

------------------------------------------------------------------------
-- dropMiddleElement, dropMiddle, and inversion for _∷_

-- dsp: lemmas
-- dsp: end of lemmas
drop-∷ : x ∷ xs ↭ x ∷ ys → xs ↭ ys
drop-∷ (refl _)    = {!!}
drop-∷ (swap _ _ _) = {!!}
drop-∷ (trans ↭₁ ↭₂) = {!!}
drop-∷ (prep _ _)   = {!!}
