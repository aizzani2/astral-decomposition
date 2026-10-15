------------------------------------------------------------------------
-- The Agda standard library
--
-- Lemmas for use in proving the polynomial homomorphism.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Bool.Base                                  using (Bool;true;false)
open import Data.Nat.Base as ℕ                              using (ℕ; suc; zero; compare; _≤′_; ≤′-step; ≤′-refl)
open import Data.Nat.Properties as ℕ                        using (≤′-trans)
open import Data.Vec.Base as Vec                            using (Vec; _∷_)
open import Data.Fin.Base                                   using (Fin; zero; suc)
open import Data.List.Base                                  using (_∷_; [])
open import Data.Unit.Base using (tt)
open import Data.List.Kleene
open import Data.Product.Base                               using (_,_; proj₁; proj₂; map₁; _×_)
open import Data.Maybe.Base                                 using (nothing; just)
open import Function.Base                                   using (_⟨_⟩_)
open import Level                                           using (lift)
open import Relation.Nullary.Decidable.Core                 using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

open Homomorphism homo hiding (_^_)
open import Tactic.RingSolver.Core.Polynomial.Reasoning to
open import Tactic.RingSolver.Core.Polynomial.Base from
open import Tactic.RingSolver.Core.Polynomial.Semantics homo

open import Algebra.Properties.Semiring.Exp.TCOptimised semiring

------------------------------------------------------------------------
-- Power lemmas
--
-- We prove some things about our odd exponentiation operator

-- First, that the optimised operator is the same as normal
-- exponentiation.
pow-opt : ∀ x ρ i → x *⟨ ρ ⟩^ i ≈ ρ ^ i * x
pow-opt x ρ zero = sym (*-identityˡ x)
pow-opt x ρ (suc i) = refl

-- Here we show a homomorphism on exponentiation, i.e. that using the
-- exponentiation function on polynomials and then evaluating is the
-- same as evaluating and then exponentiating.
-- Proving a congruence (we don't get this for free because we're using
-- setoids).
pow-mul-cong : ∀ {x y} → x ≈ y → ∀ ρ i → x *⟨ ρ ⟩^ i ≈ y *⟨ ρ ⟩^ i
pow-mul-cong x≈y ρ zero    = x≈y
pow-mul-cong x≈y ρ (suc i) = *≫ x≈y

-- Demonstrating that the proof of zeroness is correct.
zero-hom : ∀ {n} (p : Poly n) → Zero p → (ρs : Vec Carrier n) → 0# ≈ ⟦ p ⟧ ρs
zero-hom (Κ x  ⊐ i≤n) p≡0 ρs = Zero-C⟶Zero-R x p≡0

--   x¹⁺ⁿ = xxⁿ
pow-suc : ∀ x i → x ^ suc i ≈ x * x ^ i
pow-suc x zero  = sym (*-identityʳ _)
pow-suc x (suc i) = *-comm _ _

--   x¹⁺ⁿ = xⁿx
pow-sucʳ : ∀ x i → x ^ suc i ≈ x ^ i * x
pow-sucʳ x zero  = sym (*-identityˡ _)
pow-sucʳ x (suc i) = refl

-- In the proper evaluation function, we avoid ever inserting an
-- unnecessary 0# like we do here. However, it is easier to prove with
-- the form that does insert 0#. So we write one here, and then prove
-- that it's equivalent to the one that adds a 0#.
⅀?⟦_⟧ : ∀ {n} (xs : Coeff n *) → Carrier × Vec Carrier n → Carrier
⅀?⟦ []  ⟧ _ = 0#
⅀?⟦ ∹ x ⟧   = ⅀⟦ x ⟧

_⟦∷⟧?_ : ∀ {n} (x : Poly n × Coeff n *) → Carrier × Vec Carrier n → Carrier
(x , xs) ⟦∷⟧? (ρ , ρs) = ρ * ⅀?⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs

⅀?-hom : ∀ {n} (xs : Coeff n +) → ∀ ρ → ⅀?⟦ ∹ xs ⟧ ρ ≈ ⅀⟦ xs ⟧ ρ
⅀?-hom _ _ = refl

⟦∷⟧?-hom : ∀ {n} (x : Poly n) → ∀ xs ρ ρs → (x , xs) ⟦∷⟧? (ρ , ρs) ≈ (x , xs) ⟦∷⟧ (ρ , ρs)
⟦∷⟧?-hom x (∹ xs ) ρ ρs = refl
⟦∷⟧?-hom x [] ρ ρs =  (≪+ zeroʳ _) ⟨ trans ⟩ +-identityˡ _

-- dsp: lemmas
-- dsp: end of lemmas
pow′-hom : ∀ {n} i (xs : Coeff n *) → ∀ ρ ρs → ((⅀?⟦ xs ⟧ (ρ , ρs)) *⟨ ρ ⟩^ i) ≈ (⅀?⟦ xs ⍓* i ⟧ (ρ , ρs))
pow′-hom zero xs ρ ρs =  {!!}
pow′-hom (suc i) xs ρ ρs =  {!!}
