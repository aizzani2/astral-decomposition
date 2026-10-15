------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

-- The definitions of lexicographic ordering used here are suitable if
-- the argument order is a strict partial order.

{-# OPTIONS --without-K #-}

module Data.List.Relation.Binary.Lex.Strict where

open import Function.Base using (_∘_; id)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_)
open import Level using (_⊔_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles
  using (StrictPartialOrder; StrictTotalOrder; Preorder; Poset; DecPoset; DecTotalOrder)
open import Relation.Binary.Structures
  using (IsEquivalence; IsStrictPartialOrder; IsStrictTotalOrder; IsPreorder; IsPartialOrder; IsDecPartialOrder; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Irreflexive; Symmetric; _Respects₂_; Total; Asymmetric; Antisymmetric; Transitive; Trichotomous; Decidable; tri≈; tri<; tri>)
open import Relation.Binary.Consequences
open import Data.List.Relation.Binary.Pointwise as Pointwise
   using (Pointwise; []; _∷_; head; tail)

import Data.List.Relation.Binary.Lex as Core

------------------------------------------------------------------------
-- Re-exporting core definitions

open Core public
  using (Lex-<; Lex-≤; base; halt; this; next; ¬≤-this; ¬≤-next)

------------------------------------------------------------------------
-- Strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  -- Properties

  module _ {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

    private
      _≋_ = Pointwise _≈_
      _<_ = Lex-< _≈_ _≺_

    xs≮[] : ∀ {xs} → ¬ xs < []
    xs≮[] (base ())

    ¬[]<[] : ¬ [] < []
    ¬[]<[] = xs≮[]

    <-irreflexive : Irreflexive _≈_ _≺_ → Irreflexive _≋_ _<_
    <-irreflexive irr (x≈y ∷ xs≋ys) (this x<y)     = irr x≈y x<y
    <-irreflexive irr (x≈y ∷ xs≋ys) (next _ xs⊴ys) =
      <-irreflexive irr xs≋ys xs⊴ys

    <-asymmetric : Symmetric _≈_ → _≺_ Respects₂ _≈_ → Asymmetric _≺_ →
                   Asymmetric _<_
    <-asymmetric sym resp as = asym
      where
      irrefl : Irreflexive _≈_ _≺_
      irrefl = asym⇒irr resp sym as

      asym : Asymmetric _<_
      asym (base bot)       _                = bot
      asym (this x<y)       (this y<x)       = as x<y y<x
      asym (this x<y)       (next y≈x ys⊴xs) = irrefl (sym y≈x) x<y
      asym (next x≈y xs⊴ys) (this y<x)       = irrefl (sym x≈y) y<x
      asym (next x≈y xs⊴ys) (next y≈x ys⊴xs) = asym xs⊴ys ys⊴xs

    <-antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _≺_ →
                      Asymmetric _≺_ → Antisymmetric _≋_ _<_
    <-antisymmetric = Core.antisymmetric

    <-transitive : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ →
                   Transitive _≺_ → Transitive _<_
    <-transitive = Core.transitive

    <-compare : Symmetric _≈_ → Trichotomous _≈_ _≺_ →
                Trichotomous _≋_ _<_
    <-compare sym tri []       []       = tri≈ ¬[]<[] []    ¬[]<[]
    <-compare sym tri []       (y ∷ ys) = tri< halt   (λ()) (λ())
    <-compare sym tri (x ∷ xs) []       = tri> (λ())  (λ()) halt
    <-compare sym tri (x ∷ xs) (y ∷ ys) with tri x y
    ... | tri< x<y x≉y y≮x =
          tri< (this x<y) (x≉y ∘ head) (¬≤-this (x≉y ∘ sym) y≮x)
    ... | tri> x≮y x≉y y<x =
          tri> (¬≤-this x≉y x≮y) (x≉y ∘ head) (this y<x)
    ... | tri≈ x≮y x≈y y≮x with <-compare sym tri xs ys
    ...   | tri< xs<ys xs≉ys ys≮xs =
            tri< (next x≈y xs<ys) (xs≉ys ∘ tail) (¬≤-next y≮x ys≮xs)
    ...   | tri≈ xs≮ys xs≈ys ys≮xs =
            tri≈ (¬≤-next x≮y xs≮ys) (x≈y ∷ xs≈ys) (¬≤-next y≮x ys≮xs)
    ...   | tri> xs≮ys xs≉ys ys<xs =
            tri> (¬≤-next x≮y xs≮ys) (xs≉ys ∘ tail) (next (sym x≈y) ys<xs)

    <-decidable : Decidable _≈_ → Decidable _≺_ → Decidable _<_
    <-decidable = Core.decidable (no id)

    -- dsp: lemmas
    pointwiseSymmetric : IsEquivalence _≈_ → ∀ {xs ys} → xs ≋ ys → ys ≋ xs
    -- [induction] We argue by induction on xs, generalising ys, so that the induction hypothesis holds for every list ys.
    -- [case] Base case: suppose xs = []. Matching on [] forces ys = [] (the nilPointwise step), and [] ≋ [] holds.
    pointwiseSymmetric eq [] = []
    -- [case] Inductive case: suppose xs = x ∷ xs' and that the hypothesis holds for xs' and every list in place of ys. Since xs ≋ ys, we have ys = y ∷ ys' for some y and ys', with x ≈ y and xs' ≋ ys'.
    -- [step] Since ≈ is symmetric, the assumption x ≈ y gives y ≈ x.
    -- [step] By the induction hypothesis applied to xs' and ys', the relation xs' ≋ ys' gives ys' ≋ xs'.
    -- [case] Combining y ≈ x from step 4 with ys' ≋ xs' from step 5, the cons rule for ≋ gives y ∷ ys' ≋ x ∷ xs'. That is, ys ≋ xs, which completes the inductive case.
    pointwiseSymmetric eq (x≈y ∷ xs≋ys) = (IsEquivalence.sym eq x≈y ∷ pointwiseSymmetric eq xs≋ys)

    headRespect : _≺_ Respects₂ _≈_ → ∀ {x y z} → x ≈ y → x ≺ z → y ≺ z
    -- [step] The hypothesis that _≺_ respects _≈_ on both sides means, in particular, that _≺_ respects _≈_ in its first argument: for all a, b, c, if a ≈ b and a ≺ c, then b ≺ c.
    -- [step] Let x, y, z be elements with x ≈ y and x ≺ z. Apply the first-argument respect property with a = x, b = y and c = z. Its hypotheses are x ≈ y and x ≺ z, which are exactly the assumptions we have.
    -- [step] The first-argument respect property therefore yields y ≺ z, which is the required conclusion.
    headRespect resp x≈y x≺z = (resp .Data.Product.Base.proj₂ x≈y x≺z)

    leftRespect : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → ∀ {xs ys zs} → xs ≋ ys → xs < zs → ys < zs
    -- [case] Base case: xs = []. Since [] ≋ ys, the list ys must be [], and the hypothesis [] < zs is the conclusion.
    leftRespect eq resp [] xs<zs = xs<zs
    -- [case] Inductive case: xs = x ∷ xs'. From x ∷ xs' ≋ ys, ys has the form y ∷ ys' with x ≈ y and xs' ≋ ys'.
    -- [case] Since x ∷ xs' < zs, zs = z ∷ zs' for some z and zs', with x ≺ z, or x ≈ z and xs' < zs'.
    -- [case] Subcase x ≺ z. By headRespect applied to x ≈ y and x ≺ z, we get y ≺ z. Then y ∷ ys' < z ∷ zs' holds by the first clause of <.
    leftRespect eq resp (x≈y ∷ xs≋ys) (this x≺z) = (this (resp .Data.Product.Base.proj₂ x≈y x≺z))
    -- [case] Subcase x ≈ z and xs' < zs'. By the induction hypothesis applied to ys' and zs', using xs' ≋ ys' and xs' < zs', we get ys' < zs'. From x ≈ y and x ≈ z, symmetry and transitivity give y ≈ z. Then y ∷ ys' < z ∷ zs' holds by the second clause of <.
    leftRespect eq resp (x≈y ∷ xs≋ys) (next x≈z xs<zs) = (next (IsEquivalence.trans eq (IsEquivalence.sym eq x≈y) x≈z) (leftRespect eq resp xs≋ys xs<zs))

    rightRespect : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → ∀ {xs ys zs} → zs < xs → xs ≋ ys → zs < ys
    -- [induction] We argue by induction on xs. For each list xs, P(xs) is: for all ys and zs, if zs < xs and xs ≋ ys then zs < ys.
    -- [case] Base case: xs is empty, so zs < [] has no proof and the implication holds vacuously.
    rightRespect eq resp zs<xs [] = zs<xs
    -- [case] Inductive case: xs = x :: xs', and we assume P(xs'). Let ys and zs satisfy zs < x :: xs' and x :: xs' ≋ ys.
    -- [step] Since x :: xs' ≋ ys, ys = y :: ys' for some y and ys', with x ≈ y and xs' ≋ ys'.
    -- [case] Subcase (a): zs is empty. Then y :: ys' is nonempty, so the first clause of the definition gives zs < y :: ys'.
    rightRespect eq resp halt (x≈y ∷ xs≋ys) = halt
    -- [case] Subcase (b): zs = z :: zs' with z ≺ x. Since x ≈ y, the right-respect hypothesis gives z ≺ y. The second clause then gives z :: zs' < y :: ys'.
    rightRespect eq resp (this z≺x) (x≈y ∷ xs≋ys) = (this (resp .Data.Product.Base.proj₁ x≈y z≺x))
    -- [case] Subcase (c): zs = z :: zs' with z ≈ x and zs' < xs'. Transitivity of ≈ gives z ≈ y. The induction hypothesis P(xs') gives zs' < ys'. The third clause gives z :: zs' < y :: ys'.
    rightRespect eq resp (next z≈x zs'<xs') (x≈y ∷ xs≋ys) = (next (IsEquivalence.trans eq z≈x x≈y) (rightRespect eq resp zs'<xs' xs≋ys))

    -- dsp: end of lemmas
    <-respects₂ : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → _<_ Respects₂ _≋_
    -- Step 19: if xs ≋ ys then (xs < zs ⇔ ys < zs), using pointwiseSymmetric and leftRespect.
    <-respects₂ eqv resp =
      (λ p q → rightRespect eqv resp q p) ,
      (leftRespect eqv resp)
    -- Step 20: if xs ≋ ys then (zs < xs ⇔ zs < ys), using pointwiseSymmetric and rightRespect.
