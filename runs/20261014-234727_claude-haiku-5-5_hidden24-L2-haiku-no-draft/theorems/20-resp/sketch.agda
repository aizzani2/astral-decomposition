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
-- dsp: end of lemmas
∤-resp-≈ : _∤_ Respects₂ _≈_
-- No informal proof steps were provided, so this hole has no step to quote.
∤-resp-≈ = {!!}
