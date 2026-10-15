{-# OPTIONS --without-K #-}
open import Categories.Category

module Categories.Object.Product.Core {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (flip; _$_)

open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning

private
  variable
    A B C D X Y Z : Obj
    h i j : A ⇒ B

-- Borrowed from Dan Doel's definition of products
record Product (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where

  infix 10 ⟨_,_⟩

  field
    A×B   : Obj
    π₁    : A×B ⇒ A
    π₂    : A×B ⇒ B
    ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ A×B

    project₁ : π₁ ∘ ⟨ h , i ⟩ ≈ h
    project₂ : π₂ ∘ ⟨ h , i ⟩ ≈ i
    unique   : π₁ ∘ h ≈ i → π₂ ∘ h ≈ j → ⟨ i , j ⟩ ≈ h

  open Equiv

  g-η : ⟨ π₁ ∘ h , π₂ ∘ h ⟩ ≈ h
  g-η = unique refl refl

  η : ⟨ π₁ , π₂ ⟩ ≈ id
  η = unique identityʳ identityʳ

  ⟨⟩-cong₂ : ∀ {f f′ : C ⇒ A} {g g′ : C ⇒ B} → f ≈ f′ → g ≈ g′ → ⟨ f , g ⟩ ≈ ⟨ f′ , g′ ⟩
  ⟨⟩-cong₂ f≡f′ g≡g′ = unique (project₁ ○ ⟺ f≡f′) (project₂ ○ ⟺ g≡g′)

  ∘-distribʳ-⟨⟩ : ∀ {f : C ⇒ A} {g : C ⇒ B} {q : D ⇒ C} → ⟨ f , g ⟩ ∘ q ≈ ⟨ f ∘ q , g ∘ q ⟩
  ∘-distribʳ-⟨⟩ = ⟺ $ unique (pullˡ project₁) (pullˡ project₂)

  unique′ : π₁ ∘ h ≈ π₁ ∘ i → π₂ ∘ h ≈ π₂ ∘ i → h ≈ i
  unique′ eq₁ eq₂ = trans (sym (unique eq₁ eq₂)) g-η

record IsProduct {A B P} (π₁ : P ⇒ A) (π₂ : P ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  infix 10 ⟨_,_⟩

  field
    ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ P

    project₁ : π₁ ∘ ⟨ h , i ⟩ ≈ h
    project₂ : π₂ ∘ ⟨ h , i ⟩ ≈ i
    unique   : π₁ ∘ h ≈ i → π₂ ∘ h ≈ j → ⟨ i , j ⟩ ≈ h

Product⇒IsProduct : (p : Product A B) → IsProduct (Product.π₁ p) (Product.π₂ p)
Product⇒IsProduct p = record
  { ⟨_,_⟩    = ⟨_,_⟩
  ; project₁ = project₁
  ; project₂ = project₂
  ; unique   = unique
  }
  where open Product p

IsProduct⇒Product : ∀ {P} {π₁ : P ⇒ A} {π₂ : P ⇒ B} → IsProduct π₁ π₂ → Product A B
IsProduct⇒Product p = record
  { ⟨_,_⟩    = ⟨_,_⟩
  ; project₁ = project₁
  ; project₂ = project₂
  ; unique   = unique
  }
  where open IsProduct p

module _ {A B : Obj} where
  open Product {A} {B} renaming (⟨_,_⟩ to _⟨_,_⟩)

  repack : (p₁ p₂ : Product A B) → A×B p₁ ⇒ A×B p₂
  repack p₁ p₂ = p₂ ⟨ π₁ p₁ , π₂ p₁ ⟩

  repack∘ : (p₁ p₂ p₃ : Product A B) → repack p₂ p₃ ∘ repack p₁ p₂ ≈ repack p₁ p₃
  repack∘ p₁ p₂ p₃ = ⟺ $ unique p₃
    (glueTrianglesʳ (project₁ p₃) (project₁ p₂))
    (glueTrianglesʳ (project₂ p₃) (project₂ p₂))

  repack≡id : (p : Product A B) → repack p p ≈ id
  repack≡id = η

-- dsp: lemmas
mediatingUniqueness : (p : Product A B) → {X : Obj} {k k′ : X ⇒ Product.A×B p} → Product.π₁ p ∘ k ≈ Product.π₁ p ∘ k′ → Product.π₂ p ∘ k ≈ Product.π₂ p ∘ k′ → k ≈ k′
-- [step] Put f = π₁ ∘ k and g = π₂ ∘ k. By hypothesis, π₁ ∘ k′ = π₁ ∘ k = f and π₂ ∘ k′ = π₂ ∘ k = g.
-- [step] By the universal property of the product P, there exists a morphism u : X → P with π₁ ∘ u = f and π₂ ∘ u = g, and any two morphisms with these two properties are equal.
-- [case] The morphism k satisfies π₁ ∘ k = f and π₂ ∘ k = g, so k is a morphism with the properties required of u.
-- [case] The morphism k′ satisfies π₁ ∘ k′ = f and π₂ ∘ k′ = g, so k′ is also a morphism with the properties required of u.
-- [step] By the uniqueness clause in step 2, k and k′ are both equal to u, so k ≈ u and k′ ≈ u.
-- [step] By symmetry and transitivity of ≈, it follows that k ≈ k′.
mediatingUniqueness p {X} {k} {k′} eq₁ eq₂ = (Product.unique′ p eq₁ eq₂)

-- dsp: end of lemmas
up-to-iso : ∀ (p₁ p₂ : Product A B) → Product.A×B p₁ ≅ Product.A×B p₂
-- [step] Write p₁ = (A × B_{p₁}, π₁^{p₁}, π₂^{p₁}) and p₂ = (A × B_{p₂}, π₁^{p₂}, π₂^{p₂}) for the two product structures on A and B.
-- [lemma/hard] Uniqueness: if π₁ ∘ h = π₁ ∘ h′ and π₂ ∘ h = π₂ ∘ h′ then h = h′, by the universal property (mediatingUniqueness).
-- [step] Let f : A × B_{p₁} → A × B_{p₂} be the mediating morphism ⟨π₁^{p₁}, π₂^{p₁}⟩_{p₂}. By its defining equations, π₁^{p₂} ∘ f = π₁^{p₁} and π₂^{p₂} ∘ f = π₂^{p₁}.
-- [step] Let g : A × B_{p₂} → A × B_{p₁} be the mediating morphism ⟨π₁^{p₂}, π₂^{p₂}⟩_{p₁}. By its defining equations, π₁^{p₁} ∘ g = π₁^{p₂} and π₂^{p₁} ∘ g = π₂^{p₂}.
-- [step] For g ∘ f: π₁^{p₁} ∘ (g ∘ f) = (π₁^{p₁} ∘ g) ∘ f = π₁^{p₂} ∘ f = π₁^{p₁}.
-- [step] In the same way, π₂^{p₁} ∘ (g ∘ f) = (π₂^{p₁} ∘ g) ∘ f = π₂^{p₂} ∘ f = π₂^{p₁}.
-- [step] The identity satisfies π₁^{p₁} ∘ id = π₁^{p₁} and π₂^{p₁} ∘ id = π₂^{p₁} by the unit law.
-- [case] Applying mediatingUniqueness to p₁ with h = g ∘ f and h′ = id gives g ∘ f = id_{A × B_{p₁}}.
-- [case] For f ∘ g: π₁^{p₂} ∘ (f ∘ g) = (π₁^{p₂} ∘ f) ∘ g = π₁^{p₁} ∘ g = π₁^{p₂}.
-- [case] In the same way, π₂^{p₂} ∘ (f ∘ g) = (π₂^{p₂} ∘ f) ∘ g = π₂^{p₁} ∘ g = π₂^{p₂}.
-- [case] Applying mediatingUniqueness to p₂ with h = f ∘ g and h′ = id gives f ∘ g = id_{A × B_{p₂}}.
-- [step] Since f ∘ g and g ∘ f are identities, f is an isomorphism with inverse g, so A × B_{p₁} ≅ A × B_{p₂}.
up-to-iso p₁ p₂ = (record { from = repack p₁ p₂ ; to = repack p₂ p₁ ; iso = record { isoˡ = Equiv.trans (repack∘ p₁ p₂ p₁) (repack≡id p₁) ; isoʳ = Equiv.trans (repack∘ p₂ p₁ p₂) (repack≡id p₂) } })
