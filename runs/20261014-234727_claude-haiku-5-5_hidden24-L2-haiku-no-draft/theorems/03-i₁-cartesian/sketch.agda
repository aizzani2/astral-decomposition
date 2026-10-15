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
  -- The naturality square for i₁ is a pullback in any extensive category
  -- dsp: lemmas
  -- dsp: end of lemmas
  i₁-cartesian : ∀ {A B C D} (f : A ⇒ B) (g : C ⇒ D) → IsPullback f i₁ i₁ (f +₁ g)
  -- Informal proof: no steps provided.
  i₁-cartesian = (λ { f g → {!!} })
