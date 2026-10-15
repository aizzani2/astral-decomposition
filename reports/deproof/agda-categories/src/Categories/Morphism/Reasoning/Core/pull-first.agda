-- deproof: pull-first
-- agda-categories src/Categories/Morphism/Reasoning/Core.agda:315 @ fbd1259
-- An excerpt for reading: each part was checked by Agda in place, in its module.

------------------------------------------------------------------------
-- The library's proof

pull-first : f ∘ g ≈ a → f ∘ ((g ∘ h) ∘ i) ≈ a ∘ (h ∘ i)
pull-first {f = f} {g = g} {a = a} {h = h} {i = i} eq = begin
  f ∘ (g ∘ h) ∘ i ≈⟨ refl⟩∘⟨ assoc ⟩
  f ∘ g ∘ h ∘ i   ≈⟨ pullˡ eq ⟩
  a ∘ h ∘ i       ∎

------------------------------------------------------------------------
-- Its decomposition

-- pull-first : f ∘ g ≈ a → f ∘ ((g ∘ h) ∘ i) ≈ a ∘ (h ∘ i)
-- 1 clause(s), 2 step(s), lemmas: assoc, pullˡ
--
-- clause pull-first {f = f} {g = g} {a = a} {h = h} {i = i} eq
--   goal: f ∘ (g ∘ h) ∘ i ≈ a ∘ h ∘ i
--   1. f ∘ (g ∘ h) ∘ i ≈ f ∘ g ∘ h ∘ i
--        by refl⟩∘⟨ assoc   [assoc]
--   2. f ∘ g ∘ h ∘ i ≈ a ∘ h ∘ i
--        by pullˡ eq   [pullˡ]
--
-- lemmas used:
--   assoc : (h₁ ∘ g₁) ∘ f₁ ≈ h₁ ∘ g₁ ∘ f₁
--   pullˡ : C₁ ∘ f₁ ≈ g₁ → {f.X : Obj} {f = f₂ : f.X ⇒ D} → C₁ ∘ f₁ ∘ f₂ ≈ g₁ ∘ f₂

------------------------------------------------------------------------
-- Step sketch (valid, 2 hole(s))

pull-first : f ∘ g ≈ a → f ∘ ((g ∘ h) ∘ i) ≈ a ∘ (h ∘ i)
pull-first {f = f} {g = g} {a = a} {h = h} {i = i} eq = begin
  f ∘ (g ∘ h) ∘ i ≈⟨ {!!} ⟩  -- was: refl⟩∘⟨ assoc
  f ∘ g ∘ h ∘ i   ≈⟨ {!!} ⟩  -- was: pullˡ eq
  a ∘ h ∘ i       ∎

------------------------------------------------------------------------
-- Lemma sketch (valid, 2 hole(s))

-- note: no step became a lemma (step 1: a ≈ step: its statement depends on the setoid in scope; step 2: a ≈ step: its statement depends on the setoid in scope)
pull-first : f ∘ g ≈ a → f ∘ ((g ∘ h) ∘ i) ≈ a ∘ (h ∘ i)
pull-first {f = f} {g = g} {a = a} {h = h} {i = i} eq = begin
  f ∘ (g ∘ h) ∘ i ≈⟨ {!!} ⟩  -- was: refl⟩∘⟨ assoc
  f ∘ g ∘ h ∘ i   ≈⟨ {!!} ⟩  -- was: pullˡ eq
  a ∘ h ∘ i       ∎
