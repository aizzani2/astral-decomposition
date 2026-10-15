------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinatorial operations
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Nat.Combinatorics where

open import Data.Nat.Base using (ℕ; zero; suc; _!; _∸_; z≤n; s≤s; _≤_;
  _+_; _*_; _<_; s<s; ≢-nonZero)
open import Data.Nat.DivMod using (_/_; n/1≡n; /-congˡ; /-congʳ; m*n/n≡m;
  m/n/o≡m/[n*o]; n/n≡1; +-distrib-/-∣ˡ; m*n/m*o≡n/o)
open import Data.Nat.Divisibility using (_∣_; *-monoʳ-∣)
open import Data.Nat.Properties
open import Relation.Binary.Definitions using (tri>; tri≈; tri<)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong; subst)

import Data.Nat.Combinatorics.Base          as Base
import Data.Nat.Combinatorics.Specification as Specification
import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties

open ≤-Reasoning

private
  variable
    n k : ℕ

------------------------------------------------------------------------
-- Definitions

open Base public
  using (_P_; _C_)

------------------------------------------------------------------------
-- Properties of _P_

open Specification public
  using (nPk≡n!/[n∸k]!; k>n⇒nPk≡0; [n∸k]!k!∣n!)

nPn≡n! : ∀ n → n P n ≡ n !
nPn≡n! n = begin-equality
  n P n           ≡⟨ nPk≡n!/[n∸k]! (≤-refl {n}) ⟩
  n ! / (n ∸ n) ! ≡⟨ /-congʳ (cong _! (n∸n≡0 n)) ⟩
  n ! / 0 !       ≡⟨⟩
  n ! / 1         ≡⟨ n/1≡n (n !) ⟩
  n !             ∎
  where instance
    _ = (n ∸ n) !≢0

nP1≡n : ∀ n → n P 1 ≡ n
nP1≡n zero        = refl
nP1≡n n@(suc n-1) = begin-equality
  n P 1          ≡⟨ nPk≡n!/[n∸k]! (s≤s (z≤n {n-1})) ⟩
  n ! / n-1 !    ≡⟨ m*n/n≡m n (n-1 !) ⟩
  n              ∎
  where instance
    _ = n-1 !≢0

------------------------------------------------------------------------
-- Properties of _C_

open Specification public
  using (nCk≡n!/k![n-k]!; k>n⇒nCk≡0)

nCk≡nC[n∸k] : k ≤ n → n C k ≡ n C (n ∸ k)
nCk≡nC[n∸k] {k} {n} k≤n = begin-equality
  n C k                               ≡⟨ nCk≡n!/k![n-k]! k≤n ⟩
  n ! / (k ! * (n ∸ k) !)             ≡⟨ /-congʳ (*-comm ((n ∸ k) !) (k !)) ⟨
  n ! / ((n ∸ k) ! * k !)             ≡⟨ /-congʳ (cong ((n ∸ k) ! *_) (cong _! (m∸[m∸n]≡n k≤n))) ⟨
  n ! / ((n ∸ k) ! * (n ∸ (n ∸ k)) !) ≡⟨ nCk≡n!/k![n-k]! (m≤n⇒n∸m≤n k≤n) ⟨
  n C (n ∸ k)                         ∎
  where instance
    _ = (n ∸ k) !* k !≢0
    _ = k !* (n ∸ k) !≢0
    _ = (n ∸ k) !* (n ∸ (n ∸ k)) !≢0

nCk≡nPk/k! : k ≤ n → n C k ≡ ((n P k) / k !) {{k !≢0}}
nCk≡nPk/k! {k} {n} k≤n = begin-equality
  n C k                   ≡⟨ nCk≡n!/k![n-k]! k≤n ⟩
  n ! / (k ! * (n ∸ k) !) ≡⟨ /-congʳ (*-comm ((n ∸ k)!) (k !)) ⟨
  n ! / ((n ∸ k) ! * k !) ≡⟨ m/n/o≡m/[n*o] (n !) ((n ∸ k) !) (k !) ⟨
  (n ! / (n ∸ k) !) / k ! ≡⟨ /-congˡ (nPk≡n!/[n∸k]! k≤n) ⟨
  (n P k) / k !           ∎
  where instance
    _ = k !≢0
    _ = (n ∸ k) !≢0
    _ = (n ∸ k) !* k !≢0
    _ = k !* (n ∸ k) !≢0

-- dsp: lemmas
postulate
  subsetBound : ∀ (size : Set → ℕ) (m : ℕ) (Y T : Set) → size Y ≡ m → (T → Y) → size T ≤ m

postulate
  fullSubset : ∀ (size : Set → ℕ) (n : ℕ) (X S : Set) → size X ≡ n → size S ≡ n → (S → X) → (X → S)

-- dsp: end of lemmas
nCn≡1 : ∀ n → n C n ≡ 1
-- Main argument: let X be a set with n elements. The binomial coefficient n C n is the number of n-element subsets of X.
-- The set X is itself an n-element subset of X, so there is at least one n-element subset, namely X.
-- By the lemma fullSubset, every n-element subset of X equals X. So X is the only n-element subset of X.
-- Therefore the number of n-element subsets of X is exactly 1, so n C n = 1.
nCn≡1 n = {!!}
