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

  inductive⇒extensional : ∀ {n} {xs : Vec A n} {ys : Vec B n} →
                           IPointwise _∼_ xs ys → Pointwise _∼_ xs ys
  inductive⇒extensional []             = ext λ()
  inductive⇒extensional (x∼y ∷ xs∼ys) = ext λ
    { zero    → x∼y
    ; (suc i) → Pointwise.app (inductive⇒extensional xs∼ys) i
    }

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
pointwiseNil : ∀ {_∼_ : REL A B ℓ} → Pointwise _∼_ [] []
-- Step 1: Pointwise is defined by recursion on its two vector arguments, so to show Pointwise _∼_ [] [] we must exhibit the clause of the definition that applies when both vectors are empty.
-- Base case: both vectors are the empty vector of length zero. The definition of Pointwise has a clause for this pair of empty vectors, and that clause imposes no condition on the relation _∼_. Since no element pairs exist, there is nothing to check, and the clause alone gives Pointwise _∼_ [] [].
pointwiseNil = (inductive⇒extensional Inductive.[])

pointwiseConsHead : ∀ {_∼_ : REL A B ℓ} {n} {x : A} {y : B} {xs : Vec A n} {ys : Vec B n} → Pointwise _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
-- Step 2: argue by case analysis on the given proof that Pointwise relates x ∷ xs to y ∷ ys.
-- Step 3: the nil case is impossible for x ∷ xs and y ∷ ys, so it yields no clause.
-- Step 4: the remaining cons case unifies x ∷ xs with u ∷ us and y ∷ ys with v ∷ vs.
-- Step 5: the cons proof carries the head relation x ∼ y.
-- Step 6: therefore x ∼ y.
pointwiseConsHead (ext app) = (app zero)

decidableConjunction : ∀ {_∼_ : REL A B ℓ} {n} {x : A} {y : B} {xs : Vec A n} {ys : Vec B n} → Dec.Dec (x ∼ y) → Dec.Dec (Pointwise _∼_ xs ys) → Dec.Dec (Pointwise _∼_ (x ∷ xs) (y ∷ ys))
-- Step 3: Suppose P does not hold. Then P and Q does not hold, because a proof of P and Q would contain a proof of P as its first component, which contradicts the assumption that P does not hold.
decidableConjunction (Dec.no ¬p) decQ = (Dec.no (λ pw → ¬p (pointwiseConsHead pw)))
-- Step 5: Suppose Q does not hold. Then P and Q does not hold, because a proof of P and Q would contain a proof of Q as its second component, which contradicts the assumption that Q does not hold.
decidableConjunction (Dec.yes p) (Dec.no ¬q) = (Dec.no (λ pw → ¬q (tail pw)))
-- Step 6: Suppose Q holds. Together with the fact that P holds, we have a proof of P and a proof of Q, so the pair consisting of these two proofs is a proof of P and Q. Hence P and Q holds.
decidableConjunction (Dec.yes p) (Dec.yes q) = (Dec.yes (inductive⇒extensional (Inductive._∷_ p (extensional⇒inductive q))))

-- dsp: end of lemmas
decidable : ∀ {_∼_ : REL A B ℓ} → Decidable _∼_ → ∀ {n} → Decidable (Pointwise _∼_ {n = n})
-- Step 6: Base case n = 0: both vectors are empty. By lemma pointwiseNil they are pointwise related, so the decision answers yes with that proof.
decidable dec [] [] = (Dec.yes pointwiseNil)
-- Step 7: Inductive case: xs = x ∷ xs' and ys = y ∷ ys' for some x in A, y in B, and vectors xs', ys' of length n.
-- Step 8: Since the relation is decidable, decide whether x ∼ y holds, using dec.
-- Step 9: By the induction hypothesis, decide whether xs' and ys' are pointwise related.
-- Step 10: By lemmas pointwiseConsIntro, pointwiseConsHead and pointwiseConsTail, combine the two decisions with lemma decidableConjunction, giving a proof or a refutation.
-- Step 11: The induction yields an algorithm for every n.
decidable dec (x ∷ xs) (y ∷ ys) = (decidableConjunction (dec x y) (decidable dec xs ys))
