------------------------------------------------------------------------
-- The Agda standard library
--
-- Greatest common divisor
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Nat.GCD where

open import Data.Nat.Base
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Data.Nat.GCD.Lemmas
open import Data.Nat.Properties
open import Data.Nat.Induction
  using (Acc; acc; <′-Rec; <′-recBuilder; <-wellFounded-fast)
open import Data.Product.Base
  using (_×_; _,_; proj₂; proj₁; swap; uncurry′; ∃; map)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_$_; _∘_)
open import Induction using (build)
open import Induction.Lexicographic using (_⊗_; [_⊗_])
open import Relation.Binary.Definitions using (tri<; tri>; tri≈; Symmetric)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Nullary.Decidable.Core using (Dec)
open import Relation.Nullary.Negation.Core using (contradiction)
import Relation.Nullary.Decidable as Dec

open import Algebra.Definitions {A = ℕ} _≡_ as Algebra
  using (Associative; Commutative; LeftIdentity; RightIdentity; LeftZero; RightZero; Zero)

------------------------------------------------------------------------
-- Definition

-- Calculated via Euclid's algorithm. In order to show progress,
-- avoiding the initial step where the first argument may increase, it
-- is necessary to first define a version `gcd′` which assumes that the
-- second argument is strictly smaller than the first. The full `gcd`
-- function then compares the two arguments and applies `gcd′`
-- accordingly.

gcd′ : ∀ m n → Acc _<_ m → n < m → ℕ
gcd′ m zero      _         _   = m
gcd′ m n@(suc _) (acc rec) n<m = gcd′ n (m % n) (rec n<m) (m%n<n m n)

gcd : ℕ → ℕ → ℕ
gcd m n with <-cmp m n
... | tri< m<n _ _ = gcd′ n m (<-wellFounded-fast n) m<n
... | tri≈ _ _ _   = m
... | tri> _ _ n<m = gcd′ m n (<-wellFounded-fast m) n<m

------------------------------------------------------------------------
-- Core properties of gcd′

gcd′[m,n]∣m,n : ∀ {m n} rec n<m → gcd′ m n rec n<m ∣ m × gcd′ m n rec n<m ∣ n
gcd′[m,n]∣m,n {m} {zero}      rec       n<m = ∣-refl , m ∣0
gcd′[m,n]∣m,n {m} {n@(suc _)} (acc rec) n<m
  with gcd∣n , gcd∣m%n ← gcd′[m,n]∣m,n (rec n<m) (m%n<n m n)
  = ∣n∣m%n⇒∣m gcd∣n gcd∣m%n , gcd∣n

gcd′-greatest : ∀ {m n c} rec n<m → c ∣ m → c ∣ n → c ∣ gcd′ m n rec n<m
gcd′-greatest {m} {zero}      rec       n<m c∣m c∣n = c∣m
gcd′-greatest {m} {n@(suc _)} (acc rec) n<m c∣m c∣n =
  gcd′-greatest (rec n<m) (m%n<n m n) c∣n (%-presˡ-∣ c∣m c∣n)

------------------------------------------------------------------------
-- Core properties of gcd

gcd[m,n]∣m : ∀ m n → gcd m n ∣ m
gcd[m,n]∣m m n with <-cmp m n
... | tri< n<m _ _ = proj₂ (gcd′[m,n]∣m,n {n} {m} _ _)
... | tri≈ _ _ _   = ∣-refl
... | tri> _ _ m<n = proj₁ (gcd′[m,n]∣m,n {m} {n} _ _)

gcd[m,n]∣n : ∀ m n → gcd m n ∣ n
gcd[m,n]∣n m n with <-cmp m n
... | tri< n<m _    _ = proj₁ (gcd′[m,n]∣m,n {n} {m} _ _)
... | tri≈ _ ≡.refl _ = ∣-refl
... | tri> _ _    m<n = proj₂ (gcd′[m,n]∣m,n {m} {n} _ _)

gcd-greatest : ∀ {m n c} → c ∣ m → c ∣ n → c ∣ gcd m n
gcd-greatest {m} {n} c∣m c∣n with <-cmp m n
... | tri< n<m _ _ = gcd′-greatest _ _ c∣n c∣m
... | tri≈ _ _ _   = c∣m
... | tri> _ _ m<n = gcd′-greatest _ _ c∣m c∣n

------------------------------------------------------------------------
-- Other properties

-- Note that all other properties of `gcd` should be inferable from the
-- 3 core properties above.

gcd[n,n]≡n : ∀ n → gcd n n ≡ n
gcd[n,n]≡n n = ∣-antisym (gcd[m,n]∣m n n) (gcd-greatest ∣-refl ∣-refl)

gcd[m,n]≢0 : ∀ m n → m ≢ 0 ⊎ n ≢ 0 → gcd m n ≢ 0
gcd[m,n]≢0 m n (inj₁ m≢0) eq = m≢0 (0∣⇒≡0 (subst (_∣ m) eq (gcd[m,n]∣m m n)))
gcd[m,n]≢0 m n (inj₂ n≢0) eq = n≢0 (0∣⇒≡0 (subst (_∣ n) eq (gcd[m,n]∣n m n)))

-- dsp: lemmas
-- dsp: end of lemmas
gcd[m,n]≡0⇒m≡0 : ∀ {m n} → gcd m n ≡ 0 → m ≡ 0
gcd[m,n]≡0⇒m≡0 {m} {n} eq = {!!}
  where open ≡-Reasoning
