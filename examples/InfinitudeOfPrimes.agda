{-# OPTIONS --without-K #-}

module InfinitudeOfPrimes where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_)
open import Data.Product using (Σ; _×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

_∣_ : ℕ → ℕ → Set
m ∣ n = Σ[ k ∈ ℕ ] (n ≡ k * m)

IsUnit : ℕ → Set
IsUnit u = u ∣ 1

-- technically the definition of irreducibility but ℤ is a UFD so whatever
Prime : ℕ → Set
Prime p = (p ≢ 0) × (¬ IsUnit p)
        × (∀ a b → p ∣ (a * b) → (p ∣ a) ⊎ (p ∣ b))

infinitude-of-primes : ∀ (n : ℕ) → Σ[ p ∈ ℕ ] (Prime p × (n < p))
infinitude-of-primes n = ?
