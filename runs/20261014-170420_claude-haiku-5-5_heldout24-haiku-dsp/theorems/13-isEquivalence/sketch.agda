{-# OPTIONS --without-K #-}

-- Monoidal natural isomorphisms between lax and strong symmetric
-- monoidal functors.
--
-- NOTE. Symmetric monoidal natural isomorphisms are really just
-- monoidal natural isomorphisms that happen to go between symmetric
-- monoidal functors.  No additional conditions are necessary.
-- Nevertheless, the definitions in this module are useful when one is
-- working in a symmetric monoidal setting.  They also help Agda's
-- type checker by bundling the (symmetric monoidal) categories and
-- functors involved.

module Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric
  where

open import Level
open import Relation.Binary using (IsEquivalence)

open import Categories.Category.Monoidal using (SymmetricMonoidalCategory)
import Categories.Functor.Monoidal.Symmetric as SMF
open import Categories.Functor.Monoidal.Symmetric.Properties using () renaming
  ( idF-SymmetricMonoidal to idFˡ  ; idF-StrongSymmetricMonoidal to idFˢ
  ; ∘-SymmetricMonoidal   to _∘Fˡ_ ; ∘-StrongSymmetricMonoidal   to _∘Fˢ_
  )
import Categories.NaturalTransformation.Monoidal.Symmetric as SMNT
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
  using (NaturalIsomorphism)
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal as MNI

module Lax where
  open SMF.Lax using (SymmetricMonoidalFunctor)
  open MNI.Lax using (IsMonoidalNaturalIsomorphism)
  open SMNT.Lax using (SymmetricMonoidalNaturalTransformation)
  open SymmetricMonoidalFunctor using ()
    renaming (F to UF; monoidalFunctor to MF)
  private module U = MNI.Lax

  module _ {o ℓ e o′ ℓ′ e′}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′} where

    -- Monoidal natural isomorphisms between lax symmetric monoidal functors.

    record SymmetricMonoidalNaturalIsomorphism
           (F G : SymmetricMonoidalFunctor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where

      field
        U              : NaturalIsomorphism (UF F) (UF G)
        F⇒G-isMonoidal : IsMonoidalNaturalIsomorphism (MF F) (MF G) U

      ⌊_⌋ : U.MonoidalNaturalIsomorphism (MF F) (MF G)
      ⌊_⌋ = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }

      open U.MonoidalNaturalIsomorphism ⌊_⌋ public
        hiding (U; F⇒G-isMonoidal; F⇒G-monoidal; F⇐G-monoidal)

      F⇒G-monoidal : SymmetricMonoidalNaturalTransformation F G
      F⇒G-monoidal = record { U = F⇒G ; isMonoidal = F⇒G-isMonoidal }

      F⇐G-monoidal : SymmetricMonoidalNaturalTransformation G F
      F⇐G-monoidal = record { U = F⇐G ; isMonoidal = F⇐G-isMonoidal }

    infix 4 _≃_

    _≃_ = SymmetricMonoidalNaturalIsomorphism

    -- "Strengthening"

    ⌈_⌉ : {F G : SymmetricMonoidalFunctor C D} →
          U.MonoidalNaturalIsomorphism (MF F) (MF G) → F ≃ G
    ⌈ α ⌉ = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }
      where open U.MonoidalNaturalIsomorphism α

    open SymmetricMonoidalNaturalIsomorphism

    -- Identity and compositions

    infixr 9 _ⓘᵥ_

    id : {F : SymmetricMonoidalFunctor C D} → F ≃ F
    id = ⌈ U.id ⌉

    _ⓘᵥ_ : {F G H : SymmetricMonoidalFunctor C D} → G ≃ H → F ≃ G → F ≃ H
    α ⓘᵥ β   = ⌈ ⌊ α ⌋ U.ⓘᵥ ⌊ β ⌋ ⌉

    -- dsp: lemmas
    postulate
      ≃-refl : {F : SymmetricMonoidalFunctor C D} → F ≃ F

    postulate
      ≃-sym : {F G : SymmetricMonoidalFunctor C D} → F ≃ G → G ≃ F

    postulate
      ≃-trans : {F G H : SymmetricMonoidalFunctor C D} → G ≃ H → F ≃ G → F ≃ H

    -- dsp: end of lemmas
    isEquivalence : IsEquivalence _≃_
    isEquivalence = record
      { -- Step 2: "the identity natural isomorphism id : F ⇒ F is a symmetric monoidal natural isomorphism" (reflexivity).
        refl = {!!}
      ; -- Step 7: "its componentwise inverse θ⁻¹ : G ⇒ F ... is a symmetric monoidal natural isomorphism" (symmetry).
        sym = {!!}
      ; -- Step 12: "the vertical composite ψ ⓘᵥ θ, with components ψ_X ∘ θ_X, is a symmetric monoidal natural isomorphism" (transitivity).
        trans = {!!}
      }
