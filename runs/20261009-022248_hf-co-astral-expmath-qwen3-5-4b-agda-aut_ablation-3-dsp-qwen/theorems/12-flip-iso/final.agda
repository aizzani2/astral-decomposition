{-# OPTIONS --without-K #-}
open import Categories.Category

{-
  Various combinators for working with Isomorphisms in the
  context of morphism equalities
  both for Category (Switch) and IsGroupoid (GroupoidR)
-}

module Categories.Morphism.Reasoning.Iso {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Function renaming (id to idᶠ; _∘_ to _∙_)

open import Categories.Category.Groupoid using (IsGroupoid)
open import Categories.Morphism C
open import Categories.Morphism.Reasoning.Core C

open import Relation.Binary hiding (_⇒_)

open Category C
open Definitions C
private
  variable
    A B X Y : Obj
    f g h k : X ⇒ Y

open HomReasoning

module Switch (i : X ≅ Y) where
  open _≅_ i

  switch-fromtoˡ : from ∘ h ≈ k → h ≈ to ∘ k
  switch-fromtoˡ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelˡ isoˡ ⟩
    to ∘ (from ∘ h) ≈⟨ refl⟩∘⟨ pf ⟩
    to ∘ k          ∎

  switch-tofromˡ : to ∘ h ≈ k → h ≈ from ∘ k
  switch-tofromˡ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelˡ isoʳ ⟩
    from ∘ (to ∘ h) ≈⟨ refl⟩∘⟨ pf ⟩
    from ∘ k        ∎

  switch-fromtoʳ : h ∘ from ≈ k → h ≈ k ∘ to
  switch-fromtoʳ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelʳ isoʳ ⟩
    (h ∘ from) ∘ to ≈⟨ pf ⟩∘⟨refl ⟩
    k ∘ to          ∎

  switch-tofromʳ : h ∘ to ≈ k → h ≈ k ∘ from
  switch-tofromʳ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelʳ isoˡ ⟩
    (h ∘ to) ∘ from ≈⟨ pf ⟩∘⟨refl ⟩
    k ∘ from        ∎

  cancel-fromʳ : h ∘ from ≈ k ∘ from → h ≈ k
  cancel-fromʳ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelʳ isoʳ ⟩
    (h ∘ from) ∘ to ≈⟨ pf ⟩∘⟨refl ⟩
    (k ∘ from) ∘ to ≈⟨ cancelʳ isoʳ ⟩
    k               ∎

  cancel-fromˡ : from ∘ h ≈ from ∘ k → h ≈ k
  cancel-fromˡ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelˡ isoˡ ⟩
    to ∘ (from ∘ h) ≈⟨ refl⟩∘⟨ pf ⟩
    to ∘ (from ∘ k) ≈⟨ cancelˡ isoˡ ⟩
    k               ∎

  cancel-toʳ : h ∘ to ≈ k ∘ to → h ≈ k
  cancel-toʳ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelʳ isoˡ ⟩
    (h ∘ to) ∘ from ≈⟨ pf ⟩∘⟨refl ⟩
    (k ∘ to) ∘ from ≈⟨ cancelʳ isoˡ ⟩
    k               ∎

  cancel-toˡ : to ∘ h ≈ to ∘ k → h ≈ k
  cancel-toˡ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelˡ isoʳ ⟩
    from ∘ (to ∘ h) ≈⟨ refl⟩∘⟨ pf ⟩
    from ∘ (to ∘ k) ≈⟨ cancelˡ isoʳ ⟩
    k               ∎

  flip-fromˡ : from ∘ h ≈ id → h ≈ to
  flip-fromˡ {h} eq = begin
    h               ≈⟨ introˡ isoˡ ⟩
    (to ∘ from) ∘ h ≈⟨ cancelʳ eq ⟩
    to              ∎

  flip-fromʳ : h ∘ from ≈ id → h ≈ to
  flip-fromʳ {h} eq = begin
    h             ≈⟨ introʳ isoʳ ⟩
    h ∘ from ∘ to ≈⟨ cancelˡ eq ⟩
    to            ∎

  flip-toˡ : to ∘ h ≈ id → h ≈ from
  flip-toˡ {h} eq = begin
    h               ≈⟨ introˡ isoʳ ⟩
    (from ∘ to) ∘ h ≈⟨ cancelʳ eq ⟩
    from            ∎

  flip-toʳ : h ∘ to ≈ id → h ≈ from
  flip-toʳ {h} eq = begin
    h             ≈⟨ introʳ isoˡ ⟩
    h ∘ to ∘ from ≈⟨ cancelˡ eq ⟩
    from          ∎

  -- We can flip an iso i in a commuting triangle, like so:
  --
  --          i                       i⁻¹
  --    X --------> Y            X <-------- Y
  --     \    ≃    /              \    ≃    /
  --      \       /                \       /
  --     g \     / h     ===>     g \     / h
  --        \   /                    \   /
  --         V V                      V V
  --          A                        A
  --
  -- dsp: lemmas
  -- dsp: end of lemmas
  flip-iso : {g : X ⇒ A} {h : Y ⇒ A} → g ≈ h ∘ from → g ∘ to ≈ h
  flip-iso eq = Equiv.trans (∘-resp-≈ eq Equiv.refl) (cancelʳ isoʳ)
