{-# OPTIONS --without-K #-}

open import Categories.Category.Core using (Category)

module Categories.Diagram.Coequalizer {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning
open Equiv

open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open import Level
open import Function using (_$_)

private
  variable
    A B C : Obj
    h i j k : A ⇒ B

record IsCoequalizer {E} (f g : A ⇒ B) (arr : B ⇒ E) : Set (o ⊔ ℓ ⊔ e) where
  field
    equality   : arr ∘ f ≈ arr ∘ g
    coequalize : {h : B ⇒ C} → h ∘ f ≈ h ∘ g → E ⇒ C
    universal  : {h : B ⇒ C} {eq : h ∘ f ≈ h ∘ g} → h ≈ coequalize eq ∘ arr
    unique     : {h : B ⇒ C} {i : E ⇒ C} {eq : h ∘ f ≈ h ∘ g} → h ≈ i ∘ arr → i ≈ coequalize eq

  unique′ : (eq eq′ : h ∘ f ≈ h ∘ g) → coequalize eq ≈ coequalize eq′
  unique′ eq eq′ = unique universal

  id-coequalize : id ≈ coequalize equality
  id-coequalize = unique (⟺ identityˡ)

  coequalize-resp-≈ : ∀ {eq :  h ∘ f ≈ h ∘ g} {eq′ : i ∘ f ≈ i ∘ g} →
    h ≈ i → coequalize eq ≈ coequalize eq′
  coequalize-resp-≈ {h = h} {i = i} {eq = eq} {eq′ = eq′} h≈i = unique $ begin
    i                   ≈˘⟨ h≈i ⟩
    h                   ≈⟨ universal ⟩
    coequalize eq ∘ arr ∎

  coequalize-resp-≈′ : (eq :  h ∘ f ≈ h ∘ g) → (eq′ : i ∘ f ≈ i ∘ g) →
    h ≈ i → j ≈ coequalize eq → k ≈ coequalize eq′ → j ≈ k
  coequalize-resp-≈′ {j = j} {k = k} eq eq′ h≈i eqj eqk = begin
    j              ≈⟨ eqj ⟩
    coequalize eq  ≈⟨ coequalize-resp-≈ h≈i ⟩
    coequalize eq′ ≈˘⟨ eqk ⟩
    k              ∎

-- This could be proved via duality, but is easier to just write by hand,
-- as it makes the dependency graph a lot cleaner.
IsCoequalizer⇒Epi : IsCoequalizer h i j → Epi j
IsCoequalizer⇒Epi coeq _ _ eq =
  coequalize-resp-≈′ (extendˡ equality) (extendˡ equality) eq (unique refl) (unique refl)
  where
    open IsCoequalizer coeq

record Coequalizer (f g : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : Obj
    arr   : B ⇒ obj
    isCoequalizer : IsCoequalizer f g arr

  open IsCoequalizer isCoequalizer public

-- dsp: lemmas
-- dsp: end of lemmas
Coequalizer⇒Epi : (e : Coequalizer h i) → Epi (Coequalizer.arr e)
-- No informal steps were provided, so the whole proof is a single hole.
Coequalizer⇒Epi e = (λ { g₁ g₂ x → (trans (IsCoequalizer.unique (Coequalizer.isCoequalizer e) {h = g₁ ∘ Coequalizer.arr e} {i = g₁} {eq = trans assoc (trans (∘-resp-≈ refl (IsCoequalizer.equality (Coequalizer.isCoequalizer e))) (sym assoc))} refl) (sym (IsCoequalizer.unique (Coequalizer.isCoequalizer e) {h = g₁ ∘ Coequalizer.arr e} {i = g₂} {eq = trans assoc (trans (∘-resp-≈ refl (IsCoequalizer.equality (Coequalizer.isCoequalizer e))) (sym assoc))} x))) })
