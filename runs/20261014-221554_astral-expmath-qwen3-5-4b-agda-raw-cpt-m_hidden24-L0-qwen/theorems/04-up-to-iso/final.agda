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

  repack-cancel : (p₁ p₂ : Product A B) → repack p₁ p₂ ∘ repack p₂ p₁ ≈ id
  repack-cancel p₁ p₂ = repack∘ p₂ p₁ p₂ ○ repack≡id p₂

-- dsp: lemmas
-- dsp: end of lemmas
up-to-iso : ∀ (p₁ p₂ : Product A B) → Product.A×B p₁ ≅ Product.A×B p₂
up-to-iso p₁ p₂ = record
  { from = repack p₁ p₂
  ; to   = repack p₂ p₁
  ; iso  = record
    { isoˡ = repack-cancel p₂ p₁
    ; isoʳ = repack-cancel p₁ p₂
    }
  }
