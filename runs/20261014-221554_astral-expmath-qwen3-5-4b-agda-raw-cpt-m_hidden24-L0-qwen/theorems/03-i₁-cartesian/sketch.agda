{-# OPTIONS --without-K #-}

-- open import Level
open import Categories.Category.Core using (Category)

open import Data.Fin using (Fin; zero) renaming (suc to nzero)

module Categories.Category.Extensive.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Categories.Category.Extensive using (Extensive)
open import Categories.Diagram.Pullback 𝒞 using (Pullback; IsPullback; Pullback-resp-≈; unglue′) 
open import Categories.Object.Coproduct 𝒞 using (IsCoproduct; Coproduct; IsCoproduct⇒Coproduct)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

open Category 𝒞
open M 𝒞
open MR 𝒞
open HomReasoning
open Equiv

module _ (extensive : Extensive 𝒞) where
  open Extensive extensive
  open CC using (_+_; i₁; i₂; ¡; ⊥; +₁∘i₁; +₁∘i₂; ¡-unique₂; _+₁_; inject₁; inject₂; ∘-distribˡ-[]; []-cong₂; +₁∘+-swap; initial; coproducts)

  -- For coproducts with equal injections there is at most one outgoing morphism
  equal-inj : ∀ {A C D} (f : A ⇒ C) → IsCoproduct f f → (g h : C ⇒ D) → g ≈ h
  equal-inj f cp g h = sym CP.g-η ○ CP.[]-cong₂ gf≈hf gf≈hf ○ CP.g-η
    where
      module CP = Coproduct (IsCoproduct⇒Coproduct cp)
      gf≈hf = sym CP.inject₁ ○ CP.inject₂

  to-⊥-is-iso : ∀ {A} (f : A ⇒ ⊥) → IsIso f
  to-⊥-is-iso f .M.IsIso.inv = ¡
  to-⊥-is-iso f .M.IsIso.iso .M.Iso.isoʳ = ¡-unique₂ _ _
  to-⊥-is-iso f .M.IsIso.iso .M.Iso.isoˡ = equal-inj id (pullback-of-cp-is-cp' pb₁ pb₂) (¡ ∘ f) id
    where
      pb₁ : Pullback (i₁ ∘ f) i₁
      pb₁ = record
        { p₁ = id ; p₂ = f
        ; isPullback = record
            { commute         = identityʳ
            ; universal       = λ {_} {h₁} _ → h₁
            ; p₁∘universal≈h₁ = identityˡ
            ; p₂∘universal≈h₂ = λ {_} {_} {_} {eq} → pullback₁-is-mono {⊥} {⊥} _ _ (sym-assoc ○ eq)
            ; unique-diagram  = λ eq₁ _ → sym identityˡ ○ eq₁ ○ identityˡ
            } }
      pb₂ : Pullback (i₁ ∘ f) i₂
      pb₂ = record
        { p₁ = id ; p₂ = f
        ; isPullback = record
            { commute         = identityʳ ○ ∘-resp-≈ˡ (¡-unique₂ _ _)
            ; universal       = λ {_} {h₁} _ → h₁
            ; p₁∘universal≈h₁ = identityˡ
            ; p₂∘universal≈h₂ = λ {_} {_} {_} {eq} → pullback₁-is-mono {⊥} {⊥} _ _ (sym-assoc ○ eq ○ ∘-resp-≈ˡ (¡-unique₂ _ _))
            ; unique-diagram  = λ eq₁ _ → sym identityˡ ○ eq₁ ○ identityˡ
            } }

  -- The naturality square for i₁ is a pullback in any extensive category
  -- dsp: lemmas
  -- dsp: end of lemmas
  i₁-cartesian : ∀ {A B C D} (f : A ⇒ B) (g : C ⇒ D) → IsPullback f i₁ i₁ (f +₁ g)
  i₁-cartesian {A} {B} {C} {D} f g = {!!}
