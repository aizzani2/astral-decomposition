------------------------------------------------------------------------
-- The Agda standard library
--
-- Extensional pointwise lifting of relations to vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Vec.Relation.Binary.Pointwise.Extensional where

open import Data.Fin.Base using (zero; suc)
open import Data.Vec.Base as Vec hiding ([_]; head; tail; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Inductive
  using ([]; _∷_)
  renaming (Pointwise to IPointwise)
open import Level using (_⊔_)
open import Function.Base using (_∘_)
open import Function.Bundles using (module Equivalence; _⇔_; mk⇔)
open import Function.Properties.Equivalence using (⇔-setoid)
open import Level using (Level; _⊔_; 0ℓ)
open import Relation.Binary.Core using (Rel; REL; _⇒_; _=[_]⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence; IsDecEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Sym; Trans; Antisym; Decidable)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Construct.Closure.Transitive as Plus
  hiding (equivalent; map)
open import Relation.Nullary.Negation.Core using (¬_)
import Relation.Nullary.Decidable as Dec

private
  variable
    a b c ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Definition

record Pointwise {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ)
                 {n} (xs : Vec A n) (ys : Vec B n) : Set (a ⊔ b ⊔ ℓ)
                 where
  constructor ext
  field app : ∀ i → lookup xs i ∼ lookup ys i

------------------------------------------------------------------------
-- Operations

head : ∀ {_∼_ : REL A B ℓ} {n x y xs} {ys : Vec B n} →
       Pointwise _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
head (ext app) = app zero

tail : ∀ {_∼_ : REL A B ℓ} {n x y xs} {ys : Vec B n} →
       Pointwise _∼_ (x ∷ xs) (y ∷ ys) → Pointwise _∼_ xs ys
tail (ext app) = ext (app ∘ suc)

map : ∀ {_∼_ _∼′_ : REL A B ℓ} {n} →
      _∼_ ⇒ _∼′_ → Pointwise _∼_ ⇒ Pointwise _∼′_ {n}
map ∼⇒∼′ xs∼ys = ext (∼⇒∼′ ∘ Pointwise.app xs∼ys)

gmap : ∀ {_∼_ : Rel A ℓ} {_∼′_ : Rel B ℓ} {f : A → B} {n} →
       _∼_ =[ f ]⇒ _∼′_ →
       Pointwise _∼_ =[ Vec.map {n = n} f ]⇒ Pointwise _∼′_
gmap {_}          ∼⇒∼′ {[]}      {[]}      xs∼ys = ext λ()
gmap {_∼′_ = _∼′_} ∼⇒∼′ {x ∷ xs} {y ∷ ys} xs∼ys = ext λ
  { zero    → ∼⇒∼′ (head xs∼ys)
  ; (suc i) → Pointwise.app (gmap {_∼′_ = _∼′_} ∼⇒∼′ (tail xs∼ys)) i
  }

------------------------------------------------------------------------
-- The inductive and extensional definitions are equivalent.

module _ {_∼_ : REL A B ℓ} where

  extensional⇒inductive : ∀ {n} {xs : Vec A n} {ys : Vec B n} →
                           Pointwise _∼_ xs ys → IPointwise _∼_ xs ys
  extensional⇒inductive {xs = []}       {[]}   xs∼ys = []
  extensional⇒inductive {xs = x ∷ xs} {y ∷ ys} xs∼ys =
    (head xs∼ys) ∷ extensional⇒inductive (tail xs∼ys)

------------------------------------------------------------------------
-- Relational properties

refl : ∀ {_∼_ : Rel A ℓ} {n} →
       Reflexive _∼_ → Reflexive (Pointwise _∼_ {n = n})
refl ∼-rfl = ext (λ _ → ∼-rfl)

sym : ∀ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} {n} →
      Sym P Q → Sym (Pointwise P) (Pointwise Q {n = n})
sym sm xs∼ys = ext λ i → sm (Pointwise.app xs∼ys i)

trans : ∀ {P : REL A B ℓ₁} {Q : REL B C ℓ₂} {R : REL A C ℓ} {n} →
        Trans P Q R →
        Trans (Pointwise P) (Pointwise Q) (Pointwise R {n = n})
trans trns xs∼ys ys∼zs = ext λ i →
  trns (Pointwise.app xs∼ys i) (Pointwise.app ys∼zs i)

antisym : ∀ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} {R : REL A B ℓ} {n} →
          Antisym P Q R → Antisym (Pointwise P {n}) (Pointwise Q) (Pointwise R)
antisym asym xs∼ys ys∼xs = ext λ i →
  asym (Pointwise.app xs∼ys i) (Pointwise.app ys∼xs i)

-- dsp: lemmas
postulate
  pointwiseNil : ∀ {_∼_ : REL A B ℓ} → Pointwise _∼_ [] []

postulate
  pointwiseCons : ∀ {_∼_ : REL A B ℓ} {n} {x y} {xs : Vec A n} {ys : Vec B n} → x ∼ y → Pointwise _∼_ xs ys → Pointwise _∼_ (x ∷ xs) (y ∷ ys)

-- dsp: end of lemmas
decidable : ∀ {_∼_ : REL A B ℓ} → Decidable _∼_ → ∀ {n} → Decidable (Pointwise _∼_ {n = n})
-- Base case: n = 0. Both vectors are empty, and by pointwiseNil they are pointwise related. We return the affirmative answer together with this proof.
decidable dec [] [] = {!!}
-- Inductive case: suppose the claim holds for vectors of length n, and let xs and ys have length suc n. Write xs = x ∷ xs' and ys = y ∷ ys'.
-- Decide x ∼ y using decidability of ∼. Decide whether xs' and ys' are pointwise related using the induction hypothesis.
-- Positive case: if both hold, pointwiseCons gives pointwise relatedness of x ∷ xs' and y ∷ ys'.
-- Negative case, first kind: if x ∼ y is impossible, the cons vectors are not pointwise related, since head would give a proof of x ∼ y.
-- Negative case, second kind: if xs' and ys' are not pointwise related, the cons vectors are not pointwise related, since tail would give a proof that xs' and ys' are pointwise related.
-- The cases are exhaustive, so the decision for length suc n is produced.
decidable dec (x ∷ xs) (y ∷ ys) = {!!}
