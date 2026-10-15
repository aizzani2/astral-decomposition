{-# OPTIONS --without-K #-}

module Categories.NaturalTransformation.NaturalIsomorphism.Properties where

open import Level

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; flip-bifunctor)
open import Categories.Functor.Construction.LiftSetoids
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation.Properties
open import Data.Product using (_,_)

import Categories.Morphism as Mor
import Categories.Morphism.Properties as Morₚ
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e


module _ {F G : Functor C D} where
  private
    module C = Category C
    module F = Functor F
    module G = Functor G

  open Category D
  open Mor D
  open _≅_

  -- We can construct a natural isomorphism from a pointwise isomorphism, provided that we can show naturality in one direction.
  pointwise-iso : (iso : ∀ X → F.F₀ X ≅ G.F₀ X) → (∀ {X Y} → (f : C [ X , Y ]) → from (iso Y) ∘ F.F₁ f ≈ G.F₁ f ∘ from (iso X)) → NaturalIsomorphism F G
  pointwise-iso iso commute = niHelper record
    { η = λ X → from (iso X)
    ; η⁻¹ = λ X → to (iso X)
    ; commute = commute
    ; iso = λ X → record
      { isoˡ = isoˡ (iso X)
      ; isoʳ = isoʳ (iso X)
      }
    }

module _ {F G : Functor C D} (α : NaturalIsomorphism F G) where
  private module C = Category C
  open Category D
  open Mor D
  open Functor F
  open Functor G renaming (F₀ to G₀; F₁ to G₁)
  open NaturalIsomorphism α

  -- We can move equations along natural isomorphism.

  module _ {A B} {f g : A C.⇒ B} where

    push-eq : F₁ f ≈ F₁ g → G₁ f ≈ G₁ g
    push-eq hyp = MR.push-eq D FX≅GX (⇒.commute f) (⇒.commute g) hyp

    pull-eq : G₁ f ≈ G₁ g → F₁ f ≈ F₁ g
    pull-eq hyp = MR.push-eq D (≅.sym FX≅GX) (⇐.commute f) (⇐.commute g) hyp

-- properties of natural isomorphisms over an endofunctor
module _ {F : Endofunctor C} where
  private
    module C = Category C
    module F = Functor F
    module MC = Mor C

  module _ (α : F ≃ idF) where
    open C
    open HomReasoning
    open F
    open MC
    open MR C
    open Mor C
    open Morₚ C
    open NaturalIsomorphism α

    F≃id-comm₁ : ∀ {A} → ⇒.η (F₀ A) ≈ F₁ (⇒.η A)
    F≃id-comm₁ {A} = begin
      ⇒.η (F₀ A)                           ≈⟨ introʳ (F-resp-≈ (iso.isoˡ _) ○ identity) ⟩
      ⇒.η (F₀ A) ∘ F₁ (⇐.η A ∘ ⇒.η A)      ≈⟨ refl⟩∘⟨ homomorphism ⟩
      ⇒.η (F₀ A) ∘ F₁ (⇐.η A) ∘ F₁ (⇒.η A) ≈⟨ cancelˡ (⇒.commute _ ○ iso.isoˡ _) ⟩
      F₁ (⇒.η A)                           ∎

    F≃id-comm₂ : ∀ {A} → ⇐.η (F₀ A) ≈ F₁ (⇐.η A)
    F≃id-comm₂ {A} = begin
      ⇐.η (F₀ A)                             ≈⟨ introˡ (F-resp-≈ (iso.isoˡ _) ○ identity) ⟩
      F₁ (⇐.η A ∘ ⇒.η A) ∘ ⇐.η (F₀ A)        ≈⟨ homomorphism ⟩∘⟨refl ⟩
      (F₁ (⇐.η A) ∘ F₁ (⇒.η A)) ∘ ⇐.η (F₀ A) ≈⟨ cancelʳ (⟺ (⇐.commute _) ○ iso.isoˡ _) ⟩
      F₁ (⇐.η A)                             ∎

    F≃id⇒id : ∀ {A} {f : A ⇒ A} → F₁ f ≈ id → f ≈ id
    F≃id⇒id {A} {f} eq = Iso⇒Mono (Iso-swap (iso A)) _ _ helper
      where helper : ⇐.η A ∘ f ≈ ⇐.η A ∘ id
            helper = begin
              ⇐.η A ∘ f    ≈⟨ ⇐.commute f ⟩
              F₁ f ∘ ⇐.η A ≈⟨ eq ⟩∘⟨refl ⟩
              id ∘ ⇐.η A   ≈˘⟨ id-comm ⟩
              ⇐.η A ∘ id   ∎

-- properties of natural isomorphisms over bifunctors
module _ {F G : Bifunctor C D E} where

  -- dsp: lemmas
  postulate
    flip-F₁-swap : (H : Bifunctor C D E) → {X X' : Category.Obj C} {Y Y' : Category.Obj D} (f : C [ X , X' ]) (g : D [ Y , Y' ]) → E [ Functor.F₁ (flip-bifunctor H) (g , f) ≈ Functor.F₁ H (f , g) ]

  -- dsp: end of lemmas
  flip-bifunctor-NI : F ≃ G → flip-bifunctor F ≃ flip-bifunctor G
  flip-bifunctor-NI α = niHelper record
    { -- Steps 2-3: flip-bifunctor is already a functor, so no hole is needed.
    -- Step 4: β at (Y, X) is α at (X, Y).
      η = λ { (Y , X) → {!!} }
    -- Step 5: the inverse of β at (Y, X) is the inverse of α at (X, Y).
    ; η⁻¹ = λ { (Y , X) → {!!} }
    -- Steps 6-8: naturality of β, using flip-F₁-swap (step 1) and naturality of α.
    ; commute = λ { (g , f) → {!!} }
    -- Step 5: each β at (Y, X) is an isomorphism.
    ; iso = λ { (Y , X) → record
        { -- Step 5: left inverse law for β at (Y, X).
          isoˡ = {!!}
        -- Step 5: right inverse law for β at (Y, X).
        ; isoʳ = {!!}
        } }
    -- Steps 9-10: naturality of the inverses (flip-inv-commute) and the final NI assembly are handled by niHelper.
    }
