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

-- dsp: lemmas
-- dsp: end of lemmas
up-to-iso : ∀ (p₁ p₂ : Product A B) → Product.A×B p₁ ≅ Product.A×B p₂
-- Step 1: Let p₁ = (A×B₁, π₁¹, π₂¹) and p₂ = (A×B₂, π₁², π₂²) be two product structures on the objects A and B.
-- Step 2: The universal property of each product gives existence and uniqueness of mediating morphisms. In scope via the Product fields project₁, project₂ and unique.
-- Step 12: The morphisms f and g are mutually inverse, so A×B₁ ≅ A×B₂.
up-to-iso p₁ p₂ = record
  { -- Step 3: Apply the existence part of the universal property of p₂ to π₁¹ and π₂¹. This gives f : A×B₁ → A×B₂ with π₁² ∘ f = π₁¹ and π₂² ∘ f = π₂¹. This f is ⟨π₁¹, π₂¹⟩_{p₂}.
    from = (repack p₁ p₂)
  ; -- Step 4: Apply the existence part of the universal property of p₁ to π₁² and π₂². This gives g : A×B₂ → A×B₁ with π₁¹ ∘ g = π₁² and π₂¹ ∘ g = π₂². This g is ⟨π₁², π₂²⟩_{p₁}.
    to = (repack p₂ p₁)
  ; iso = record
    { -- Steps 5-8: Show g ∘ f has components π₁¹ and π₂¹ with respect to p₁, using associativity and the defining equations of f and g. Then the uniqueness part of the universal property of p₁ gives g ∘ f = id.
      isoˡ = (Product.unique′ p₁ (Equiv.trans sym-assoc (Equiv.trans (∘-resp-≈ˡ (Product.project₁ p₁)) (Equiv.trans (Product.project₁ p₂) (Equiv.sym identityʳ)))) (Equiv.trans sym-assoc (Equiv.trans (∘-resp-≈ˡ (Product.project₂ p₁)) (Equiv.trans (Product.project₂ p₂) (Equiv.sym identityʳ)))))
    ; -- Steps 9-11: Show f ∘ g has components π₁² and π₂² with respect to p₂, using associativity and the defining equations of f and g. Then the uniqueness part of the universal property of p₂ gives f ∘ g = id.
      isoʳ = (Product.unique′ p₂ (Equiv.trans sym-assoc (Equiv.trans (∘-resp-≈ˡ (Product.project₁ p₂)) (Equiv.trans (Product.project₁ p₁) (Equiv.sym identityʳ)))) (Equiv.trans sym-assoc (Equiv.trans (∘-resp-≈ˡ (Product.project₂ p₂)) (Equiv.trans (Product.project₂ p₁) (Equiv.sym identityʳ)))))
    }
  }
