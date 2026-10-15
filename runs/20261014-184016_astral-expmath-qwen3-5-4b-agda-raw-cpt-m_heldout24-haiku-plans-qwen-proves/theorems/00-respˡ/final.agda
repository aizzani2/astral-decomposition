------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of binary operators to binary relations via the right
-- natural order.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Algebra.Core using (Op₂)
open import Data.Product.Base using (_,_; _×_)
open import Data.Sum.Base using (inj₁; inj₂; map)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles
  using (Preorder; Poset; DecPoset; TotalOrder; DecTotalOrder)
open import Relation.Binary.Structures
  using (IsEquivalence; IsPreorder; IsPartialOrder; IsDecPartialOrder
        ; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Symmetric; Transitive; Reflexive; Antisymmetric; Total; _Respectsʳ_
        ; _Respectsˡ_; _Respects₂_; Decidable)

open import Relation.Nullary.Negation using (¬_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

module Relation.Binary.Construct.NaturalOrder.Right
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A) where

open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Algebra.Lattice.Structures _≈_

------------------------------------------------------------------------
-- Definition

infix 4 _≤_

_≤_ : Rel A ℓ
x ≤ y = x ≈ (y ∙ x)

------------------------------------------------------------------------
-- Relational properties

reflexive : IsMagma _∙_ → Idempotent _∙_ → _≈_ ⇒ _≤_
reflexive magma idem {x} {y} x≈y = begin
  x     ≈⟨ sym (idem x) ⟩
  x ∙ x ≈⟨ ∙-cong x≈y refl ⟩
  y ∙ x ∎
  where open IsMagma magma; open ≈-Reasoning setoid

refl : Symmetric _≈_ → Idempotent _∙_ → Reflexive _≤_
refl sym idem {x} = sym (idem x)

antisym : IsEquivalence _≈_ → Commutative _∙_ → Antisymmetric _≈_ _≤_
antisym isEq comm {x} {y} x≤y y≤x = begin
  x     ≈⟨  x≤y ⟩
  y ∙ x ≈⟨  comm y x ⟩
  x ∙ y ≈⟨ y≤x ⟨
  y     ∎
  where open ≈-Reasoning (record { isEquivalence = isEq })

total : Symmetric _≈_ → Transitive _≈_ → Selective _∙_ → Commutative _∙_ → Total _≤_
total sym trans sel comm x y =
  map (λ x∙y≈x → trans (sym x∙y≈x) (comm x y)) sym (sel x y)

trans : IsSemigroup _∙_ → Transitive _≤_
trans semi {x} {y} {z} x≤y y≤z = begin
  x           ≈⟨ x≤y ⟩
  y ∙ x       ≈⟨ ∙-cong y≤z S.refl ⟩
  (z ∙ y) ∙ x ≈⟨ assoc z y x ⟩
  z ∙ (y ∙ x) ≈⟨ ∙-cong S.refl (sym x≤y) ⟩
  z ∙ x       ∎
  where open module S = IsSemigroup semi; open ≈-Reasoning S.setoid

respʳ : IsMagma _∙_ → _≤_ Respectsʳ _≈_
respʳ magma {x} {y} {z} y≈z x≤y = begin
  x     ≈⟨ x≤y ⟩
  y ∙ x ≈⟨ ∙-cong y≈z M.refl ⟩
  z ∙ x ∎
  where open module M = IsMagma magma; open ≈-Reasoning M.setoid

-- dsp: lemmas
-- dsp: end of lemmas
respˡ : IsMagma _∙_ → _≤_ Respectsˡ _≈_
respˡ magma {x} {y} {z} y≈z x≤y = (M.trans (sym y≈z) (M.trans x≤y (∙-cong M.refl y≈z)))
  where open module M = IsMagma magma; open ≈-Reasoning M.setoid
