{-# OPTIONS --without-K #-}

open import Categories.Bicategory using (Bicategory)

module Categories.Bicategory.Extras {o ℓ e t} (Bicat : Bicategory o ℓ e t) where

open import Data.Product using (_,_)

import Categories.Category.Construction.Core as Core
open import Categories.Category.Construction.Functors using (Functors; module curry)
open import Categories.Functor using (Functor)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.Functor.Bifunctor using (flip-bifunctor)
open import Categories.Functor.Bifunctor.Properties
open import Categories.NaturalTransformation
  using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties using (push-eq)

open Bicategory Bicat public
private
  variable
    A B C D : Obj
    f g h i : A ⇒₁ B
    α β γ δ α′ β′ γ′ δ′ : f ⇒₂ g

infixr 10 _▷ᵢ_
infixl 10 _◁ᵢ_
infixr 6  _⟩⊚⟨_ refl⟩⊚⟨_
infixl 7  _⟩⊚⟨refl

module ⊚ {A B C}          = Functor (⊚ {A} {B} {C})
module ⊚-assoc {A B C D}  = NaturalIsomorphism (⊚-assoc {A} {B} {C} {D})
module unitˡ {A B}        = NaturalIsomorphism (unitˡ {A} {B})
module unitʳ {A B}        = NaturalIsomorphism (unitʳ {A} {B})
module id {A}             = Functor (id {A})

private
  module MR′ {A} {B} where
    open Core.Shorthands (hom A B) public
    open MR (hom A B) public hiding (push-eq)
  open MR′

unitorˡ : {A B : Obj} {f : A ⇒₁ B} → id₁ ∘₁ f ≅ f
unitorˡ {_} {_} {f} = record
  { from = unitˡ.⇒.η (_ , f)
  ; to   = unitˡ.⇐.η (_ , f)
  ; iso  = unitˡ.iso (_ , f)
  }

module unitorˡ {A B f} = _≅_ (unitorˡ {A} {B} {f})

unitorʳ : {A B : Obj} {f : A ⇒₁ B} → f ∘₁ id₁ ≅ f
unitorʳ {_} {_} {f} = record
  { from = unitʳ.⇒.η (f , _)
  ; to   = unitʳ.⇐.η (f , _)
  ; iso  = unitʳ.iso (f , _)
  }

module unitorʳ {A B f} = _≅_ (unitorʳ {A} {B} {f})

associator : {A B C D : Obj} {f : D ⇒₁ B} {g : C ⇒₁ D} {h : A ⇒₁ C} →
             (f ∘₁ g) ∘₁ h ≅ f ∘₁ g ∘₁ h
associator {_} {_} {_} {_} {f} {g} {h} = record
  { from = ⊚-assoc.⇒.η ((f , g) , h)
  ; to   = ⊚-assoc.⇐.η ((f , g) , h)
  ; iso  = ⊚-assoc.iso ((f , g) , h)
  }

module associator {A B C D} {f : C ⇒₁ B} {g : D ⇒₁ C} {h} = _≅_ (associator {A = A} {B = B} {f = f} {g = g} {h = h})

module Shorthands where
  λ⇒ = unitorˡ.from
  λ⇐ = unitorˡ.to

  ρ⇒ = unitorʳ.from
  ρ⇐ = unitorʳ.to

  α⇒ = associator.from
  α⇐ = associator.to
open Shorthands

-- Two curried versions of ⊚.

-⊚[-] : Functor (hom A B) (Functors (hom B C) (hom A C))
-⊚[-] = curry.F₀ (flip-bifunctor ⊚)

[-]⊚- : Functor (hom B C) (Functors (hom A B) (hom A C))
[-]⊚- = curry.F₀ ⊚

-⊚_ : A ⇒₁ B → Functor (hom B C) (hom A C)
-⊚_ = Functor.F₀ -⊚[-]

_⊚- : B ⇒₁ C → Functor (hom A B) (hom A C)
_⊚- = Functor.F₀ [-]⊚-

-▷_ : ∀ {C} → f ⇒₂ g → NaturalTransformation (-⊚_ {C = C} f) (-⊚ g)
-▷_ = Functor.F₁ -⊚[-]

_◁- : ∀ {A} → f ⇒₂ g → NaturalTransformation (_⊚- {A = A} f) (g ⊚-)
_◁- = Functor.F₁ [-]⊚-

identity₂ˡ : id₂ ∘ᵥ α ≈ α
identity₂ˡ = hom.identityˡ

identity₂ʳ : α ∘ᵥ id₂ ≈ α
identity₂ʳ = hom.identityʳ

identity₂² : id₂ ∘ᵥ id₂ {f = g} ≈ id₂ {f = g}
identity₂² = hom.identity²

assoc₂ : (α ∘ᵥ β) ∘ᵥ γ ≈ α ∘ᵥ β ∘ᵥ γ
assoc₂ = hom.assoc

sym-assoc₂ : α ∘ᵥ β ∘ᵥ γ ≈ (α ∘ᵥ β) ∘ᵥ γ
sym-assoc₂ = hom.sym-assoc

id₂◁ : id₂ {f = g} ◁ f ≈ id₂
id₂◁ = ⊚.identity

▷id₂ : f ▷ id₂ {f = g} ≈ id₂
▷id₂ = ⊚.identity

open hom.HomReasoning
open hom.Equiv

_⊚ᵢ_ : f ≅ h → g ≅ i → f ⊚₀ g ≅ h ⊚₀ i
α ⊚ᵢ β = record
  { from = from α ⊚₁ from β
  ; to   = to α ⊚₁ to β
  ; iso  = record
    { isoˡ = [ ⊚ ]-merge (isoˡ α) (isoˡ β) ○ ⊚.identity
    ; isoʳ = [ ⊚ ]-merge (isoʳ α) (isoʳ β) ○ ⊚.identity }
  }

_◁ᵢ_ : {g h : B ⇒₁ C} (α : g ≅ h) (f : A ⇒₁ B) → g ∘₁ f ≅ h ∘₁ f
α ◁ᵢ _ = α ⊚ᵢ idᵢ

_▷ᵢ_ : {f g : A ⇒₁ B} (h : B ⇒₁ C) (α : f ≅ g) → h ∘₁ f ≅ h ∘₁ g
_ ▷ᵢ α = idᵢ ⊚ᵢ α

⊚-resp-≈ : α ≈ β → γ ≈ δ → α ⊚₁ γ ≈ β ⊚₁ δ
⊚-resp-≈ p q = ⊚.F-resp-≈ (p , q)

⊚-resp-≈ˡ : α ≈ β → α ⊚₁ γ ≈ β ⊚₁ γ
⊚-resp-≈ˡ p = ⊚.F-resp-≈ (p , hom.Equiv.refl)

⊚-resp-≈ʳ : γ ≈ δ → α ⊚₁ γ ≈ α ⊚₁ δ
⊚-resp-≈ʳ q = ⊚.F-resp-≈ (hom.Equiv.refl , q)

_⟩⊚⟨_ : α ≈ β → γ ≈ δ → α ⊚₁ γ ≈ β ⊚₁ δ
_⟩⊚⟨_ = ⊚-resp-≈

refl⟩⊚⟨_ : γ ≈ δ → α ⊚₁ γ ≈ α ⊚₁ δ
refl⟩⊚⟨_ = ⊚-resp-≈ʳ

_⟩⊚⟨refl : α ≈ β → α ⊚₁ γ ≈ β ⊚₁ γ
_⟩⊚⟨refl = ⊚-resp-≈ˡ

⊚-resp-sq : α ∘ᵥ β ≈ α′ ∘ᵥ β′ → γ ∘ᵥ δ ≈ γ′ ∘ᵥ δ′
          → α ⊚₁ γ ∘ᵥ β ⊚₁ δ ≈ α′ ⊚₁ γ′ ∘ᵥ β′ ⊚₁ δ′
⊚-resp-sq sqˡ sqʳ = [ ⊚ ]-resp-square (sqˡ , sqʳ)

⊚-resp-sqˡ-degen : α ∘ᵥ β ≈ α′ ∘ᵥ β′ → α ◁ f ∘ᵥ β ⊚₁ δ ≈ α′ ⊚₁ δ ∘ᵥ β′ ◁ g
⊚-resp-sqˡ-degen sq = ⊚-resp-sq sq (toSquare refl)

⊚-resp-sqˡ-degen′ : α ∘ᵥ β ≈ α′ ∘ᵥ β′ → α ⊚₁ γ ∘ᵥ β ◁ g ≈ α′ ◁ f ∘ᵥ β′ ⊚₁ γ
⊚-resp-sqˡ-degen′ sq = ⊚-resp-sq sq (⟺ (toSquare refl))

⊚-resp-sqʳ-degen : γ ∘ᵥ δ ≈ γ′ ∘ᵥ δ′ → f ▷ γ ∘ᵥ β ⊚₁ δ ≈ β ⊚₁ γ′ ∘ᵥ g ▷ δ′
⊚-resp-sqʳ-degen sq = ⊚-resp-sq (toSquare refl) sq

⊚-resp-sqʳ-degen′ : γ ∘ᵥ δ ≈ γ′ ∘ᵥ δ′ → α ⊚₁ γ ∘ᵥ g  ▷ δ ≈ f ▷ γ′ ∘ᵥ α ⊚₁ δ′
⊚-resp-sqʳ-degen′ sq = ⊚-resp-sq (⟺ (toSquare refl)) sq

∘ᵥ-distr-⊚ : (α ∘ᵥ γ) ⊚₁ (β ∘ᵥ δ) ≈ (α ⊚₁ β) ∘ᵥ (γ ⊚₁ δ)
∘ᵥ-distr-⊚ = Functor.homomorphism ⊚

α⇐-⊚ : α⇐ ∘ᵥ (α ⊚₁ β ⊚₁ γ) ≈ ((α ⊚₁ β) ⊚₁ γ) ∘ᵥ α⇐
α⇐-⊚ {α = α} {β = β} {γ = γ} = ⊚-assoc.⇐.commute ((α , β) , γ)

α⇒-⊚ : α⇒ ∘ᵥ ((α ⊚₁ β) ⊚₁ γ) ≈ (α ⊚₁ β ⊚₁ γ) ∘ᵥ α⇒
α⇒-⊚ {α = α} {β = β} {γ = γ} = ⊚-assoc.⇒.commute ((α , β) , γ)

∘ᵥ-distr-◁ : (α ◁ f) ∘ᵥ (β ◁ f) ≈ (α ∘ᵥ β) ◁ f
∘ᵥ-distr-◁ {f = f} = ⟺ (Functor.homomorphism (-⊚ f))

∘ᵥ-distr-▷ : (f ▷ α) ∘ᵥ (f ▷ β) ≈ f ▷ (α ∘ᵥ β)
∘ᵥ-distr-▷ {f = f} = ⟺ (Functor.homomorphism (f ⊚-))

◁-resp-≈ : α ≈ β → α ◁ f ≈ β ◁ f
◁-resp-≈ = _⟩⊚⟨refl

▷-resp-≈ : α ≈ β → f ▷ α ≈ f ▷ β
▷-resp-≈ = refl⟩⊚⟨_

◁-resp-tri : α ∘ᵥ β ≈ γ → α ◁ f ∘ᵥ β ◁ f ≈ γ ◁ f
◁-resp-tri {α = α} {β = β} {γ = γ} {f = f} tri = begin
  α ◁ f ∘ᵥ β ◁ f ≈⟨ ∘ᵥ-distr-◁ ⟩
  (α ∘ᵥ β) ◁ f   ≈⟨ ◁-resp-≈ tri ⟩
  γ ◁ f          ∎

▷-resp-tri : α ∘ᵥ β ≈ γ → f ▷ α ∘ᵥ f ▷ β ≈ f ▷ γ
▷-resp-tri {α = α} {β = β} {γ = γ} {f = f} tri = begin
  f ▷ α ∘ᵥ f ▷ β ≈⟨ ∘ᵥ-distr-▷ ⟩
  f ▷ (α ∘ᵥ β)   ≈⟨ ▷-resp-≈ tri ⟩
  f ▷ γ          ∎

◁-resp-sq : α ∘ᵥ β ≈ γ ∘ᵥ δ → α ◁ f ∘ᵥ β ◁ f ≈ γ ◁ f ∘ᵥ δ ◁ f
◁-resp-sq {α = α} {β = β} {γ = γ} {δ = δ} {f = f} sq = begin
  α ◁ f ∘ᵥ β ◁ f ≈⟨ ∘ᵥ-distr-◁ ⟩
  (α ∘ᵥ β) ◁ f   ≈⟨ ◁-resp-≈ sq ⟩
  (γ ∘ᵥ δ)◁ f    ≈⟨ ⟺ ∘ᵥ-distr-◁ ⟩
  γ ◁ f ∘ᵥ δ ◁ f ∎

▷-resp-sq : α ∘ᵥ β ≈ γ ∘ᵥ δ → f ▷ α ∘ᵥ f ▷ β ≈ f ▷ γ ∘ᵥ f ▷ δ
▷-resp-sq {α = α} {β = β} {γ = γ} {δ = δ} {f = f} sq = begin
  f ▷ α ∘ᵥ f ▷ β ≈⟨ ∘ᵥ-distr-▷ ⟩
  f ▷ (α ∘ᵥ β)   ≈⟨ ▷-resp-≈ sq ⟩
  f ▷ (γ ∘ᵥ δ)   ≈⟨ ⟺ ∘ᵥ-distr-▷ ⟩
  f ▷ γ ∘ᵥ f ▷ δ ∎

▷-resp-long-sq : α ∘ᵥ β ∘ᵥ γ ≈ (β′ ∘ᵥ γ′) ∘ᵥ α′ → f ▷ α ∘ᵥ f ▷ β ∘ᵥ f ▷ γ ≈ (f ▷ β′ ∘ᵥ f ▷ γ′) ∘ᵥ f ▷ α′
▷-resp-long-sq {α = α} {β = β} {γ = γ} {β′ = β′} {γ′ = γ′} {α′ = α′} {f = f} sq = begin
  f ▷ α ∘ᵥ f ▷ β ∘ᵥ f ▷ γ      ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
  f ▷ α ∘ᵥ f ▷ (β ∘ᵥ γ)        ≈⟨ ▷-resp-sq sq ⟩
  f ▷ (β′ ∘ᵥ γ′) ∘ᵥ f ▷ α′     ≈⟨ ⟺ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
  (f ▷ β′ ∘ᵥ f ▷ γ′) ∘ᵥ f ▷ α′ ∎

▷-resp-long-sq′ : (α ∘ᵥ β) ∘ᵥ γ ≈ γ′ ∘ᵥ (α′ ∘ᵥ β′) → (f ▷ α ∘ᵥ f ▷ β) ∘ᵥ f ▷ γ ≈ f ▷ γ′ ∘ᵥ f ▷ α′ ∘ᵥ f ▷ β′
▷-resp-long-sq′ {α = α} {β = β} {γ = γ} {γ′ = γ′} {α′ = α′} {β′ = β′} {f = f} sq = begin
  (f ▷ α ∘ᵥ f ▷ β) ∘ᵥ f ▷ γ    ≈⟨ ∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
  f ▷ (α ∘ᵥ β) ∘ᵥ f ▷ γ        ≈⟨ ▷-resp-sq sq ⟩
  f ▷ γ′ ∘ᵥ f ▷ (α′ ∘ᵥ β′)     ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩
  f ▷ γ′ ∘ᵥ (f ▷ α′ ∘ᵥ f ▷ β′) ∎

◁-resp-long-sq : α ∘ᵥ β ∘ᵥ γ ≈ (β′ ∘ᵥ γ′) ∘ᵥ α′ → α ◁ f ∘ᵥ β ◁ f ∘ᵥ γ ◁ f ≈ (β′ ◁ f ∘ᵥ γ′ ◁ f) ∘ᵥ α′ ◁ f
◁-resp-long-sq {α = α} {β = β} {γ = γ} {β′ = β′} {γ′ = γ′} {α′ = α′} {f = f} sq = begin
  α ◁ f ∘ᵥ β ◁ f ∘ᵥ γ ◁ f      ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
  α ◁ f ∘ᵥ (β ∘ᵥ γ) ◁ f        ≈⟨ ◁-resp-sq sq ⟩
  (β′ ∘ᵥ γ′) ◁ f ∘ᵥ α′ ◁ f     ≈⟨ ⟺ ∘ᵥ-distr-◁ ⟩∘⟨refl  ⟩
  (β′ ◁ f ∘ᵥ γ′ ◁ f) ∘ᵥ α′ ◁ f ∎

◁-resp-long-sq′ : (α ∘ᵥ β) ∘ᵥ γ ≈ γ′ ∘ᵥ (α′ ∘ᵥ β′) → (α ◁ f ∘ᵥ β ◁ f) ∘ᵥ γ ◁ f ≈ γ′ ◁ f ∘ᵥ α′ ◁ f ∘ᵥ β′ ◁ f
◁-resp-long-sq′ {α = α} {β = β} {γ = γ} {γ′ = γ′} {α′ = α′} {β′ = β′} {f = f} sq = begin
  (α ◁ f ∘ᵥ β ◁ f) ∘ᵥ γ ◁ f    ≈⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩
  (α ∘ᵥ β) ◁ f ∘ᵥ γ ◁ f        ≈⟨ ◁-resp-sq sq ⟩
  γ′ ◁ f ∘ᵥ (α′ ∘ᵥ β′) ◁ f     ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
  γ′ ◁ f ∘ᵥ (α′ ◁ f ∘ᵥ β′ ◁ f) ∎

λ⇒-∘ᵥ-▷ : λ⇒ ∘ᵥ (id₁ ▷ α) ≈ α ∘ᵥ λ⇒
λ⇒-∘ᵥ-▷ {α = α} = begin
  λ⇒ ∘ᵥ (id₁ ▷ α)    ≈˘⟨ refl⟩∘⟨ id.identity ⟩⊚⟨refl ⟩
  λ⇒ ∘ᵥ id.F₁ _ ⊚₁ α ≈⟨ unitˡ.⇒.commute (_ , α) ⟩
  α ∘ᵥ λ⇒            ∎

▷-∘ᵥ-λ⇐ : (id₁ ▷ α) ∘ᵥ λ⇐ ≈ λ⇐ ∘ᵥ α
▷-∘ᵥ-λ⇐ = conjugate-to (unitorˡ ⁻¹) (unitorˡ ⁻¹) λ⇒-∘ᵥ-▷

ρ⇒-∘ᵥ-◁ : ρ⇒ ∘ᵥ (α ◁ id₁) ≈ α ∘ᵥ ρ⇒
ρ⇒-∘ᵥ-◁ {α = α} = begin
  ρ⇒ ∘ᵥ (α ◁ id₁)      ≈˘⟨ refl⟩∘⟨ refl⟩⊚⟨ id.identity ⟩
  ρ⇒ ∘ᵥ (α ⊚₁ id.F₁ _) ≈⟨ unitʳ.⇒.commute (α , _) ⟩
  α ∘ᵥ ρ⇒              ∎

◁-∘ᵥ-ρ⇐ : (α ◁ id₁) ∘ᵥ ρ⇐ ≈ ρ⇐ ∘ᵥ α
◁-∘ᵥ-ρ⇐ = conjugate-to (unitorʳ ⁻¹) (unitorʳ ⁻¹) ρ⇒-∘ᵥ-◁

α⇐-◁-∘₁ : α⇐ ∘ᵥ (γ ◁ (g ∘₁ f)) ≈ ((γ ◁ g) ◁ f) ∘ᵥ α⇐
α⇐-◁-∘₁ {γ = γ} {g = g} {f = f} = begin
  α⇐ ∘ᵥ (γ ◁ (g ∘₁ f))    ≈˘⟨ refl⟩∘⟨ refl⟩⊚⟨ ⊚.identity ⟩
  α⇐ ∘ᵥ (γ ⊚₁ id₂ ⊚₁ id₂)  ≈⟨ ⊚-assoc.⇐.commute ((γ , id₂) , id₂) ⟩
  ((γ ◁ g) ◁ f) ∘ᵥ α⇐      ∎

α⇒-◁-∘₁ : α⇒ ∘ᵥ γ ◁ g ◁ f ≈ γ ◁ (g ∘₁ f) ∘ᵥ α⇒
α⇒-◁-∘₁ = ⟺ (conjugate-to associator associator α⇐-◁-∘₁)

-- dsp: lemmas
-- dsp: end of lemmas
α⇐-▷-◁ : α⇐ ∘ᵥ (f ▷ (γ ◁ g)) ≈ ((f ▷ γ) ◁ g) ∘ᵥ α⇐
α⇐-▷-◁ {γ = γ} = {!!}
