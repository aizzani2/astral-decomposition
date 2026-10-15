------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of same-length vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Vec.Relation.Binary.Lex.Core {a} {A : Set a} where

open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Properties as ℕ using (_≡?_; ≡-irrelevant)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
open import Function.Base using (flip)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel; REL)
open import Relation.Binary.Definitions
  using (Transitive; Symmetric; Asymmetric; Antisymmetric; Irreflexive; Trans
        ; _Respects₂_; _Respectsˡ_; _Respectsʳ_; Decidable; Irrelevant)
open import Relation.Binary.Structures using (IsPartialEquivalence)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; refl; cong)
import Relation.Nullary as Nullary
open import Relation.Nullary.Decidable as Dec using (Dec; yes; no; _×?_; _⊎?_)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

private
  variable
    ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Definition

-- The lexicographic ordering itself can be either strict or non-strict,
-- depending on whether type P is inhabited.

data Lex {A : Set a} (P : Set) (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂)
       : ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂) where
  base : (p : P) → Lex P _≈_ _≺_ [] []
  this : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n}
         (x≺y : x ≺ y) (m≡n : m ≡ n) → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)
  next : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n}
         (x≈y : x ≈ y) (xs<ys : Lex P _≈_ _≺_ xs ys) → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)

------------------------------------------------------------------------
-- Operations

map-P : ∀ {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} {P₁ P₂ : Set} → (P₁ → P₂) →
        ∀ {m n} {xs : Vec A m} {ys : Vec A n} →
        Lex P₁ _≈_ _≺_ xs ys → Lex P₂ _≈_ _≺_ xs ys
map-P f (base p)         = base (f p)
map-P f (this x≺y m≡n)   = this x≺y m≡n
map-P f (next x≈y xs<ys) = next x≈y (map-P f xs<ys)

------------------------------------------------------------------------
-- Properties

module _ {P : Set} {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

module _ {P : Set} {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

  private
    _≋_ = Pointwise _≈_
    _<ₗₑₓ_ = Lex P _≈_ _≺_

  ≰-this : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n} →
           ¬ (x ≈ y) → ¬ (x ≺ y) → ¬ (x ∷ xs) <ₗₑₓ (y ∷ ys)
  ≰-this x≉y x≮y (this x≺y m≡n)   = contradiction x≺y x≮y
  ≰-this x≉y x≮y (next x≈y xs<ys) = contradiction x≈y x≉y

  ≰-next : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n} →
           ¬ (x ≺ y) → ¬ (xs <ₗₑₓ ys) → ¬ (x ∷ xs) <ₗₑₓ (y ∷ ys)
  ≰-next x≮y xs≮ys (this x≺y m≡n)   = contradiction x≺y x≮y
  ≰-next x≮y xs≮ys (next x≈y xs<ys) = contradiction xs<ys xs≮ys

  module _ (≈-equiv : IsPartialEquivalence _≈_)
           ((≺-respʳ-≈ , ≺-respˡ-≈) : _≺_ Respects₂ _≈_)
           (≺-trans : Transitive _≺_)
           (open IsPartialEquivalence ≈-equiv)
           where

  module _ (≈-sym : Symmetric _≈_) (≺-irrefl : Irreflexive _≈_ _≺_) (≺-asym : Asymmetric _≺_) where

    antisym : ∀ {n} → Antisymmetric (_≋_ {n}) (_<ₗₑₓ_)
    antisym (base _)         (base _)         = []
    antisym (this x≺y m≡n)   (this y≺x n≡m)   = contradiction y≺x (≺-asym x≺y)
    antisym (this x≺y m≡n)   (next y≈x ys<xs) = contradiction x≺y (≺-irrefl (≈-sym y≈x))
    antisym (next x≈y xs<ys) (this y≺x m≡n)   = contradiction y≺x (≺-irrefl (≈-sym x≈y))
    antisym (next x≈y xs<ys) (next y≈x ys<xs) = x≈y ∷ (antisym xs<ys ys<xs)

  module _ (≈-equiv : IsPartialEquivalence _≈_) (open IsPartialEquivalence ≈-equiv) where

    respectsˡ : _≺_ Respectsˡ _≈_ → ∀ {m n} → (_<ₗₑₓ_ {m} {n}) Respectsˡ _≋_
    respectsˡ resp []            (base p)         = base p
    respectsˡ resp (x≈y ∷ xs≋ys) (this x≺z m≡n)   = this (resp x≈y x≺z) m≡n
    respectsˡ resp (x≈y ∷ xs≋ys) (next x≈z xs<zs) = next (trans (sym x≈y) x≈z) (respectsˡ resp xs≋ys xs<zs)

    respectsʳ : _≺_ Respectsʳ _≈_ → ∀ {m n} → (_<ₗₑₓ_ {m} {n}) Respectsʳ _≋_
    respectsʳ resp [] (base p)                    = base p
    respectsʳ resp (x≈y ∷ xs≋ys) (this x≺z m≡n)   = this (resp x≈y x≺z) m≡n
    respectsʳ resp (x≈y ∷ xs≋ys) (next x≈z xs<zs) = next (trans x≈z x≈y) (respectsʳ resp xs≋ys xs<zs)

    respects₂ : _≺_ Respects₂ _≈_ → ∀ {n} → (_<ₗₑₓ_ {n} {n}) Respects₂ _≋_
    respects₂ (≺-resp-≈ʳ , ≺-resp-≈ˡ) = respectsʳ ≺-resp-≈ʳ , respectsˡ ≺-resp-≈ˡ

  module _ (P? : Dec P) (_≈?_ : Decidable _≈_) (_≺?_ : Decidable _≺_) where

    -- dsp: lemmas
    -- dsp: end of lemmas
    decidable : ∀ {m n} → Decidable (_<ₗₑₓ_ {m} {n})
    -- No informal proof steps were provided, so this is a single placeholder hole.
    decidable = {!!}
