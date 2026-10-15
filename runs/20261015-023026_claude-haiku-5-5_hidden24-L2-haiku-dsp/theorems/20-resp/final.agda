------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility over magmas
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Algebra.Bundles using (Magma)

module Algebra.Properties.Magma.Divisibility {a ℓ} (M : Magma a ℓ) where

open import Data.Product.Base using (_,_; swap)
open import Relation.Binary.Definitions
  using (_Respects_; _Respectsˡ_; _Respectsʳ_; _Respects₂_; Symmetric)
open import Relation.Nullary.Negation.Core using (contradiction)

open Magma M

------------------------------------------------------------------------
-- Re-export divisibility relations publicly

open import Algebra.Definitions.RawMagma rawMagma public
  using (_∣_; _∤_; _∥_; _∦_; _∣ˡ_; _∤ˡ_; _∣ʳ_; _∤ʳ_; _,_)

------------------------------------------------------------------------
-- Properties of right divisibility

x∣ʳyx : ∀ x y → x ∣ʳ y ∙ x
x∣ʳyx x y = y , refl

xy≈z⇒y∣ʳz : ∀ x y {z} → x ∙ y ≈ z → y ∣ʳ z
xy≈z⇒y∣ʳz x y xy≈z = x , xy≈z

------------------------------------------------------------------------
-- Properties of left divisibility

∣ˡ-respʳ-≈ : _∣ˡ_ Respectsʳ _≈_
∣ˡ-respʳ-≈ y≈z (q , xq≈y) = q , trans xq≈y y≈z

∣ˡ-respˡ-≈ : _∣ˡ_ Respectsˡ _≈_
∣ˡ-respˡ-≈ x≈z (q , xq≈y) = q , trans (∙-congʳ (sym x≈z)) xq≈y

∣ˡ-resp-≈ : _∣ˡ_ Respects₂ _≈_
∣ˡ-resp-≈ = ∣ˡ-respʳ-≈ , ∣ˡ-respˡ-≈

x∣ˡxy : ∀ x y → x ∣ˡ x ∙ y
x∣ˡxy x y = y , refl

xy≈z⇒x∣ˡz : ∀ x y {z} → x ∙ y ≈ z → x ∣ˡ z
xy≈z⇒x∣ˡz x y xy≈z = y , xy≈z

------------------------------------------------------------------------
-- Properties of non-divisibility

-- dsp: lemmas
nmidRespectsFirst : (x y z : Carrier) → x ≈ y → x ∤ z → y ∤ z
-- Step 3: suppose for contradiction that some q satisfies q · y ≈ z (the witness and proof are bound by the pattern).
-- Steps 4-5: from x ≈ y and mulRespectsEq, get q · x ≈ q · y; with q · y ≈ z, transitivity gives q · x ≈ z.
-- Step 6: this q witnesses x ∣ z, contradicting x ∤ z.
-- Step 7: the supposition is impossible, so no q satisfies q · y ≈ z; hence y ∤ z.
nmidRespectsFirst x y z x≈y x∤z (q , qy≈z) = (x∤z (q , trans (∙-cong refl x≈y) qy≈z))

nmidRespectsSecond : (x y z : Carrier) → x ≈ y → z ∤ x → z ∤ y
-- Step 1: Assume z ∤ x and x ≈ y. To prove z ∤ y, suppose some q satisfies q · z ≈ y.
-- Step 2: From the assumption x ≈ y, symmetry of ≈ gives y ≈ x.
-- Step 3: We have q · z ≈ y and y ≈ x. By transitivity of ≈, q · z ≈ x.
-- Step 4: So q witnesses z ∣ x, which contradicts the assumption z ∤ x.
-- Step 5: The supposition is impossible. Hence no q satisfies q · z ≈ y, so z ∤ y.
nmidRespectsSecond x y z x≈y z∤x (q , qz≈y) = (z∤x (q , trans qz≈y (sym x≈y)))

-- dsp: end of lemmas
∤-resp-≈ : _∤_ Respects₂ _≈_
∤-resp-≈ =
  -- Step 11: ∤ respects ≈ in its right (dividend) argument, via lemma nmidRespectsSecond.
  (λ {w} {u} {v} → nmidRespectsSecond u v w)
  ,
  -- Step 11: ∤ respects ≈ in its left (divisor) argument, via lemma nmidRespectsFirst.
  (λ {w} {u} {v} → nmidRespectsFirst u v w)
