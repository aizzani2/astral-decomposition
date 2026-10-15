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
record Coequalizer (f g : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : Obj
    arr   : B ⇒ obj
    isCoequalizer : IsCoequalizer f g arr

  open IsCoequalizer isCoequalizer public

-- dsp: lemmas
precompositionCoequalizes : (e : Coequalizer h i) {C : Obj} (w : Coequalizer.obj e ⇒ C) → (w ∘ Coequalizer.arr e) ∘ h ≈ (w ∘ Coequalizer.arr e) ∘ i
-- Step 1: g ∘ h ≈ g ∘ i (g = Coequalizer.arr e) by the defining property of the coequalizer.
-- Step 2: (w ∘ g) ∘ h ≈ w ∘ (g ∘ h) by associativity of composition.
-- Step 3: (w ∘ g) ∘ i ≈ w ∘ (g ∘ i) by associativity of composition.
-- Step 4: w ∘ (g ∘ h) ≈ w ∘ (g ∘ i) by congruence of the fixed morphism w applied to step 1.
-- Step 5: chain steps 2, 4, and 3 to get (w ∘ g) ∘ h ≈ (w ∘ g) ∘ i.
precompositionCoequalizes e w = (trans assoc (trans (∘-resp-≈ refl (Coequalizer.equality e)) (sym assoc)))

-- dsp: end of lemmas
Coequalizer⇒Epi : (e : Coequalizer h i) → Epi (Coequalizer.arr e)
-- Step 1: Write g for e.arr so that g ∘ h ≈ g ∘ i. Let C be an object and let u, v : e.obj → C with u ∘ g ≈ v ∘ g. We must show u ≈ v.
-- Step 2: For any w : e.obj → C, (w ∘ g) ∘ h ≈ (w ∘ g) ∘ i, by associativity and g ∘ h ≈ g ∘ i (precompositionCoequalizes).
-- Step 3: Let f = u ∘ g. By precompositionCoequalizes with w = u, f ∘ h ≈ f ∘ i.
-- Step 4: By the universal property of the coequalizer e, there exists k : e.obj → C with k ∘ g ≈ f.
-- Step 5: u ∘ g ≈ f, by the definition of f.
-- Step 6: v ∘ g ≈ f, because v ∘ g ≈ u ∘ g = f by hypothesis.
-- Step 7: By uniqueness, u ≈ k and v ≈ k.
-- Step 8: Combining u ≈ k and k ≈ v gives u ≈ v, so arr is an epimorphism.
Coequalizer⇒Epi e = (λ { g₁ g₂ x → (trans (Coequalizer.unique e {h = g₁ ∘ Coequalizer.arr e} {i = g₁} {eq = precompositionCoequalizes e g₁} refl) (sym (Coequalizer.unique e {h = g₁ ∘ Coequalizer.arr e} {i = g₂} {eq = precompositionCoequalizes e g₁} x))) })
