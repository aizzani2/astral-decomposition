-- deproof: +-comm
-- agda-stdlib src/Data/Nat/Properties.agda:567 @ 47beb93
-- An excerpt for reading: each part was checked by Agda in place, in its module.

------------------------------------------------------------------------
-- The library's proof

+-comm : Commutative _+_
+-comm zero    n = sym (+-identityʳ n)
+-comm (suc m) n = begin-equality
  suc m + n   ≡⟨⟩
  suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m) ≡⟨ sym (+-suc n m) ⟩
  n + suc m   ∎

------------------------------------------------------------------------
-- Its decomposition

-- +-comm : Commutative _+_
-- 2 clause(s), 3 step(s) (+1 by computation or refl), lemmas: +-identityʳ, +-suc
--
-- clause +-comm zero n
--   goal: zero + n ≡ n + zero
--   1. zero + n ≡ n + zero
--        by sym (+-identityʳ n)   [+-identityʳ]
--
-- clause +-comm (suc m) n
--   goal: suc m + n ≡ n + suc m
--   1. suc m + n ≡ suc (m + n)
--        by computation
--   2. suc (m + n) ≡ suc (n + m)
--        by cong suc (+-comm m n)   [IH]
--   3. suc (n + m) ≡ n + suc m
--        by sym (+-suc n m)   [+-suc]
--
-- lemmas used:
--   +-identityʳ : RightIdentity 0 _+_
--   +-suc : (m₁ n₁ : ℕ) → m₁ + suc n₁ ≡ suc (m₁ + n₁)

------------------------------------------------------------------------
-- Step sketch (valid, 3 hole(s))

+-comm : Commutative _+_
+-comm zero    n = -- was: sym (+-identityʳ n)
  {!!}
+-comm (suc m) n = begin-equality
  suc m + n   ≡⟨⟩
  suc (m + n) ≡⟨ {!!} ⟩  -- was: cong suc (+-comm m n)
  suc (n + m) ≡⟨ {!!} ⟩  -- was: sym (+-suc n m)
  n + suc m   ∎

------------------------------------------------------------------------
-- Lemma sketch (valid, 3 hole(s); lemmas +-comm-lemma1, +-comm-lemma2)

+-comm-lemma1 : (n : ℕ) → zero + n ≡ n + zero
-- was: sym (+-identityʳ n)
+-comm-lemma1 n = {!!}
+-comm-lemma2 : (m : ℕ) → (n : ℕ) → suc (n + m) ≡ n + suc m
+-comm-lemma2 m n = {!!}
+-comm : Commutative _+_
+-comm zero    n = +-comm-lemma1 n
+-comm (suc m) n = begin-equality
  suc m + n   ≡⟨⟩
  suc (m + n) ≡⟨ {!!} ⟩  -- was: cong suc (+-comm m n)
  suc (n + m) ≡⟨ +-comm-lemma2 m n ⟩
  n + suc m   ∎
