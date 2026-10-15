------------------------------------------------------------------------
-- The Agda standard library
--
-- The specification for combinatorics operations
------------------------------------------------------------------------
-- This module should not be imported directly! Please use
-- `Data.Nat.Combinatorics` instead.

{-# OPTIONS --without-K #-}

module Data.Nat.Combinatorics.Specification where

open import Data.Bool.Base using (T; true; false)
open import Data.Nat.Base using (zero; suc; _≤ᵇ_; _≤_; _!; _∸_; pred;
  >-nonZero; _*_; NonZero; _+_; s≤s; z≤n; _>_)
open import Data.Nat.DivMod using (_/_; n/n≡1; /-congʳ; m*n/m!≡n/[m∸1]!;
  *-/-assoc; n/1≡n; m/n/o≡m/[n*o]; /-congˡ)
open import Data.Nat.Divisibility using (m≤n⇒m!∣n!; _∣_; ∣-refl;
  ∣-reflexive; module ∣-Reasoning; ∣m∣n⇒∣m+n; *-monoʳ-∣; m∣n/o⇒o*m∣n)
open import Data.Nat.Properties
open import Data.Nat.Combinatorics.Base using (_P′_; _P_; _C′_; _C_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (yes; no; does)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; trans; _≢_; subst; refl; sym; cong; cong₂)

import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as *-CS

------------------------------------------------------------------------
-- Prelude

private
  ≤ᵇ⇒≤′ : ∀ {m n} → (m ≤ᵇ n) ≡ true → m ≤ n
  ≤ᵇ⇒≤′ {m} {n} eq = ≤ᵇ⇒≤ m n (subst T (sym eq) _)

------------------------------------------------------------------------
-- Properties of _P′_

nP′k≡n[n∸1P′k∸1] : ∀ n k → .{{NonZero n}} → .{{NonZero k}} →
                   n P′ k ≡ n * (pred n P′ pred k)
nP′k≡n[n∸1P′k∸1] n           (suc zero)            = refl
nP′k≡n[n∸1P′k∸1] n@(suc n-1) k@(suc k-1@(suc k-2)) = begin-equality
  n P′ k                        ≡⟨⟩
  (n ∸ k-1) * (n P′ k-1)        ≡⟨ cong ((n ∸ k-1) *_) (nP′k≡n[n∸1P′k∸1] n k-1) ⟩
  (n ∸ k-1) * (n * (n-1 P′ k-2))  ≡⟨ x∙yz≈y∙xz (n ∸ k-1) n (n-1 P′ k-2) ⟩
  n * ((n ∸ k-1) * (n-1 P′ k-2))  ≡⟨⟩
  n * (n-1 P′ k-1)              ∎
  where open ≤-Reasoning; open *-CS

P′-rec : ∀ {n k} → k ≤ n → .{{NonZero k}} →
        n P′ k ≡ k * (pred n P′ pred k) + pred n P′ k
P′-rec n@{suc n-1} k@{suc k-1} k≤n = begin-equality
  n P′ k                                        ≡⟨ nP′k≡n[n∸1P′k∸1] n k ⟩
  n * (n-1 P′ k-1)                              ≡⟨ cong (_* (n-1 P′ k-1)) (m+[n∸m]≡n {k} {n} k≤n) ⟨
  (k + (n ∸ k)) * (n-1 P′ k-1)                  ≡⟨ *-distribʳ-+ (n-1 P′ k-1) k (n ∸ k) ⟩
  k * (n-1 P′ k-1) + (n-1 ∸ k-1) * (n-1 P′ k-1) ≡⟨⟩
  k * (n-1 P′ k-1) + (n-1 P′ k)                 ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _P_

k>n⇒nPk≡0 : ∀ {n k} → k > n → n P k ≡ 0
k>n⇒nPk≡0 {n} {k} k>n with k ≤ᵇ n in eq
... | true  = contradiction (≤ᵇ⇒≤′ eq) (<⇒≱ k>n)
... | false = refl

------------------------------------------------------------------------
-- Properties of _C′_

-- dsp: lemmas
postulate
  complementSize : ∀ {n k} → k ≤ n → k + (n ∸ k) ≡ n

postulate
  complementInvolution : ∀ {n k} → k ≤ n → n ∸ (n ∸ k) ≡ k

postulate
  C′-zeroʳ : ∀ n → n C′ zero ≡ 1

postulate
  C′-self : ∀ n → n C′ n ≡ 1

postulate
  C′-pascal : ∀ n k → (suc n) C′ (suc k) ≡ (n C′ k) + (n C′ (suc k))

-- dsp: end of lemmas
C′-sym : ∀ {n k} → k ≤ n → n C′ (n ∸ k) ≡ n C′ k
-- Step 1: Fix n and k with k ≤ n. Here n = 0 forces k = 0, so 0 ∸ 0 = 0 and both sides are 0 C′ 0.
C′-sym {zero} {zero} z≤n = {!!}
-- Step 1: With n = 0 and k = j + 1, the proof of k ≤ n is impossible, so this case does not arise.
C′-sym {zero} {suc j} ()
-- Step 4 (k = 0): the map S ↦ S^c sends the empty subset to X, so both sides count 1, by C′-self and C′-zeroʳ.
C′-sym {suc n} {zero} z≤n = {!!}
-- Steps 2 to 5: the complement map S ↦ S^c, using complementSize and complementInvolution, is a bijection between k-element and (n − k)-element subsets, so the cardinalities agree; prove by induction on n using C′-pascal. Step 6: the reversed equation is the same statement.
C′-sym {suc n} {suc k} (s≤s p) = {!!}
