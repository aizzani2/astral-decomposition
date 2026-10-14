{-# OPTIONS --without-K #-}

module Categories.Adjoint.TwoSided where

-- A "two sided" adjoint is an adjoint of two functors L and R where the
-- unit and counit are natural isomorphisms.

-- A two sided adjoint is the underlying data to an Adjoint Equivalence
open import Level

open import Categories.Adjoint
open import Categories.Category.Core using (Category)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism as ≃ using (_≃_; NaturalIsomorphism)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e    : Level
    o′ ℓ′ e′ : Level
    C D      : Category o ℓ e

infix 5 _⊣⊢_

record _⊣⊢_ (L : Functor C D) (R : Functor D C) : Set (levelOfTerm L ⊔ levelOfTerm R) where
  field
    unit   : idF ≃ (R ∘F L)
    counit : (L ∘F R) ≃ idF

  module unit   = NaturalIsomorphism unit
  module counit = NaturalIsomorphism counit

  private
    module C = Category C using (Obj; id; _∘_; _≈_; module HomReasoning)
    module D = Category D using (Obj; id; _∘_; _≈_; module HomReasoning)
    module L = Functor L using (₀; ₁; op; identity)
    module R = Functor R using (₀; ₁; op; identity)

  field
    zig : ∀ {A : C.Obj} → counit.⇒.η (L.₀ A) D.∘ L.₁ (unit.⇒.η A) D.≈ D.id
    zag : ∀ {B : D.Obj} → R.₁ (counit.⇒.η B) C.∘ unit.⇒.η (R.₀ B) C.≈ C.id

  op₁ : R.op ⊣⊢ L.op
  op₁ = record
    { unit   = counit.op
    ; counit = unit.op
    ; zig    = zag
    ; zag    = zig
    }

  zag⁻¹ : {B : D.Obj} → unit.⇐.η (R.₀ B) C.∘ R.₁ (counit.⇐.η B) C.≈ C.id
  zag⁻¹ {B} = begin
    unit.⇐.η (R.₀ B) C.∘ R.₁ (counit.⇐.η B)   ≈˘⟨ flip-fromʳ unit.FX≅GX zag ⟩∘⟨refl ⟩
    R.₁ (counit.⇒.η B) C.∘ R.₁ (counit.⇐.η B) ≈⟨ [ R ]-resp-inverse (counit.iso.isoʳ B) ⟩
    C.id                                      ∎
    where open C.HomReasoning
          open MR C

  -- dsp: lemmas
  -- dsp: end of lemmas
  zig⁻¹ : {A : C.Obj} → L.₁ (unit.⇐.η A) D.∘ counit.⇐.η (L.₀ A) D.≈ D.id
  -- No informal proof steps were provided.
  zig⁻¹ = {!!}
