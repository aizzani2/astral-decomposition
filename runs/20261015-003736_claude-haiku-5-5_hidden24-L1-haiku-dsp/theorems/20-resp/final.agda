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

∣ʳ-respʳ-≈ : _∣ʳ_ Respectsʳ _≈_
∣ʳ-respʳ-≈ y≈z (q , qx≈y) = q , trans qx≈y y≈z

∣ʳ-respˡ-≈ : _∣ʳ_ Respectsˡ _≈_
∣ʳ-respˡ-≈ x≈z (q , qx≈y) = q , trans (∙-congˡ (sym x≈z)) qx≈y

∣ʳ-resp-≈ : _∣ʳ_ Respects₂ _≈_
∣ʳ-resp-≈ = ∣ʳ-respʳ-≈ , ∣ʳ-respˡ-≈

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
-- dsp: end of lemmas
∤-resp-≈ : _∤_ Respects₂ _≈_
-- Steps 1 and 11: ≈ is an equivalence, and ∤ respects ≈ in both arguments.
∤-resp-≈ = (λ {a} {b} {c} b≈c p →
  -- Steps 7-10: let z ∤ x and x ≈ y; show z ∤ y.
  -- Suppose z ∤ y fails, so q · z ≈ y. Symmetry and transitivity give q · z ≈ x, contradicting z ∤ x.
  (λ { (q , qa≈c) → p (q , trans qa≈c (sym b≈c)) })) ,
  (λ {b} {a} {c} a≈c p →
  -- Steps 2-6: let x ≈ y and x ∤ z; show y ∤ z.
  -- Suppose y ∤ z fails, so q · y ≈ z. Congruence and transitivity give q · x ≈ z, contradicting x ∤ z.
  (λ { (q , qc≈b) → p (q , trans (∙-cong refl a≈c) qc≈b) }))
