------------------------------------------------------------------------
-- The Agda standard library
--
-- A generalisation of the arithmetic operations
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Nat.GeneralisedArithmetic where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; *-identityˡ; *-assoc)
open import Function.Base using (_∘′_; _∘_; id)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

private
  variable
    a : Level
    A : Set a

fold : A → (A → A) → ℕ → A
fold z s zero    = z
fold z s (suc n) = s (fold z s n)

iterate : (A → A) → A → ℕ → A
iterate f x zero    = x
iterate f x (suc n) = iterate f (f x) n

add : (0# : A) (1+ : A → A) → ℕ → A → A
add 0# 1+ n z = fold z 1+ n

mul : (0# : A) (1+ : A → A) → (+ : A → A → A) → (ℕ → A → A)
mul 0# 1+ _+_ n x = fold 0# (λ s → x + s) n

-- Properties

fold-+ : ∀ (z : A) (s : A → A) m {n} →
         fold z s (m + n) ≡ fold (fold z s n) s m
fold-+ z s zero    = refl
fold-+ z s (suc m) = cong s (fold-+ z s m)

fold-k : ∀ (z : A) (s : A → A) {k} m →
         fold k (s ∘′_) m z ≡ fold (k z) s m
fold-k z s zero    = refl
fold-k z s (suc m) = cong s (fold-k z s m)

fold-* : ∀ (z : A) (s : A → A) m {n} →
         fold z s (m * n) ≡ fold z (fold id (s ∘_) n) m
fold-* z s zero        = refl
fold-* z s (suc m) {n} = let +n = fold id (s ∘′_) n in begin
  fold z s (n + m * n)        ≡⟨ fold-+ z s n ⟩
  fold (fold z s (m * n)) s n ≡⟨ cong (λ z → fold z s n) (fold-* z s m) ⟩
  fold (fold z +n m) s n      ≡⟨ sym (fold-k _ s n) ⟩
  fold z +n (suc m)           ∎

fold-pull : ∀ (z : A) (s : A → A) (g : A → A → A) (p : A)
            (eqz : g z p ≡ p)
            (eqs : ∀ l → s (g l p) ≡ g (s l) p) →
            ∀ m → fold p s m ≡ g (fold z s m) p
fold-pull z s _ _ eqz _ zero    = sym eqz
fold-pull z s g p eqz eqs (suc m) = begin
  s (fold p s m)       ≡⟨ cong s (fold-pull z s g p eqz eqs m) ⟩
  s (g (fold z s m) p) ≡⟨ eqs (fold z s m) ⟩
  g (s (fold z s m)) p ∎

iterate-is-fold : ∀ (z : A) s m → fold z s m ≡ iterate s z m
iterate-is-fold z s zero    = refl
iterate-is-fold z s (suc m) = begin
  fold z s (suc m)  ≡⟨ cong (fold z s) (+-comm 1 m) ⟩
  fold z s (m + 1)  ≡⟨ fold-+ z s m ⟩
  fold (s z) s m    ≡⟨ iterate-is-fold (s z) s m ⟩
  iterate s (s z) m ∎

id-is-fold : ∀ m → fold zero suc m ≡ m
id-is-fold zero    = refl
id-is-fold (suc m) = cong suc (id-is-fold m)

+-is-fold : ∀ m {n} → fold n suc m ≡ m + n
+-is-fold zero    = refl
+-is-fold (suc m) = cong suc (+-is-fold m)

*-is-fold : ∀ m {n} → fold zero (n +_) m ≡ m * n
*-is-fold zero        = refl
*-is-fold (suc m) {n} = cong (n +_) (*-is-fold m)

^-is-fold : ∀ {m} n → fold 1 (m *_) n ≡ m ^ n
^-is-fold     zero    = refl
^-is-fold {m} (suc n) = cong (m *_) (^-is-fold n)

-- dsp: lemmas
plusAssoc : (a b c : ℕ) → a + (b + c) ≡ (a + b) + c
-- Induction on a, holding b and c fixed.
-- Base case: when a is zero, the left side 0 + (b + c) reduces to b + c, and the right side (0 + b) + c reduces to b + c, so the two sides are equal.
plusAssoc zero b c = refl
-- Inductive case: assume a + (b + c) = (a + b) + c. Then suc a + (b + c) reduces to suc (a + (b + c)), which by the induction hypothesis equals suc ((a + b) + c).
-- The right side (suc a + b) + c reduces, since suc a + b reduces to suc (a + b), to suc (a + b) + c, which reduces to suc ((a + b) + c).
-- Comparing the two reductions, suc a + (b + c) and (suc a + b) + c both equal suc ((a + b) + c), so they are equal.
plusAssoc (suc a) b c = (cong suc (plusAssoc a b c))

sucMulEq : (m n : ℕ) → suc m * n ≡ n + m * n
-- Step 2: suc m * n matches the second defining clause of multiplication, giving n + m * n. Step 3: the right-hand side is already n + m * n, so both sides are equal. No induction is needed.
sucMulEq m n = refl

isfold-gap1 : (m : ℕ) → (n : ℕ) → {p : ℕ} → fold p (_+_ n) (suc m) ≡ suc m * n + p
-- Base case: not stated in the informal proof.
isfold-gap1 zero n {p} = (cong (_+ p) (sym (Data.Nat.Properties.+-identityʳ n)))
-- 1. [case] Inductive case: assume that fold p (n +) m = m * n + p holds for the given m, where n and p are fixed. We must show fold p (n +) (suc m) = suc m * n + p.
-- 2. [case] By the defining equation of fold on a successor, fold p (n +) (suc m) equals n + fold p (n +) m.
-- 3. [case] Applying the induction hypothesis to the right-hand summand, n + fold p (n +) m equals n + (m * n + p).
-- 4. [case] By the associativity of addition, applied with a = n, b = m * n and c = p, we have n + (m * n + p) = (n + (m * n)) + p.
-- 5. [lemma/hard] By the defining equation of multiplication on a successor, suc m * n equals n + (m * n), so n + (m * n) = suc m * n.
-- 6. [case] Substituting the equality from the previous step into (n + (m * n)) + p gives (suc m * n) + p. Chaining steps 2 to 6 yields fold p (n +) (suc m) = suc m * n + p, which completes the inductive case.
isfold-gap1 (suc m) n {p} = (begin fold p (_+_ n) (suc (suc m)) ≡⟨ cong (n +_) (isfold-gap1 m n {p}) ⟩ n + (suc m * n + p) ≡⟨ plusAssoc n (suc m * n) p ⟩ (n + suc m * n) + p ≡⟨ cong (_+ p) (sym (sucMulEq (suc m) n)) ⟩ suc (suc m) * n + p ∎)

-- dsp: end of lemmas
*+-is-fold : ∀ m n {p} → fold p (n +_) m ≡ m * n + p
-- Base case: F(0) = p. By step 4, 0 * n = 0, so 0 * n + p reduces to 0 + p, which reduces to p.
*+-is-fold zero n = refl
-- Inductive case: assume F(m) = m * n + p. Then F(suc m) = n + (m * n + p), which by plusAssoc with a = n, b = m * n, c = p equals (n + (m * n)) + p. By step 4, n + (m * n) = suc m * n, so F(suc m) = (suc m) * n + p.
*+-is-fold (suc m) n = (isfold-gap1 m n)
