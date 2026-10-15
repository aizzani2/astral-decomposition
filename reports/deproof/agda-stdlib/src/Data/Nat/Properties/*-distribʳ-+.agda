-- deproof: *-distribʳ-+
-- agda-stdlib src/Data/Nat/Properties.agda:817 @ 47beb93
-- An excerpt for reading: each part was checked by Agda in place, in its module.

------------------------------------------------------------------------
-- The library's proof

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ m zero    o = refl
*-distribʳ-+ m (suc n) o = begin-equality
  (suc n + o) * m     ≡⟨⟩
  m + (n + o) * m     ≡⟨ cong (m +_) (*-distribʳ-+ m n o) ⟩
  m + (n * m + o * m) ≡⟨ sym (+-assoc m (n * m) (o * m)) ⟩
  m + n * m + o * m   ≡⟨⟩
  suc n * m + o * m   ∎

------------------------------------------------------------------------
-- Its decomposition

-- *-distribʳ-+ : _*_ DistributesOverʳ _+_
-- 2 clause(s), 2 step(s) (+3 by computation or refl), lemmas: +-assoc
--
-- clause *-distribʳ-+ m zero o
--   goal: (zero + o) * m ≡ zero * m + o * m
--   1. (zero + o) * m ≡ zero * m + o * m
--        by refl
--
-- clause *-distribʳ-+ m (suc n) o
--   goal: (suc n + o) * m ≡ suc n * m + o * m
--   1. (suc n + o) * m ≡ m + (n + o) * m
--        by computation
--   2. m + (n + o) * m ≡ m + (n * m + o * m)
--        by cong (m +_) (*-distribʳ-+ m n o)   [IH]
--   3. m + (n * m + o * m) ≡ m + n * m + o * m
--        by sym (+-assoc m (n * m) (o * m))   [+-assoc]
--   4. m + n * m + o * m ≡ suc n * m + o * m
--        by computation
--
-- lemmas used:
--   +-assoc : Associative _+_

------------------------------------------------------------------------
-- Step sketch (valid, 3 hole(s))

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ m zero    o = -- was: refl
  {!!}
*-distribʳ-+ m (suc n) o = begin-equality
  (suc n + o) * m     ≡⟨⟩
  m + (n + o) * m     ≡⟨ {!!} ⟩  -- was: cong (m +_) (*-distribʳ-+ m n o)
  m + (n * m + o * m) ≡⟨ {!!} ⟩  -- was: sym (+-assoc m (n * m) (o * m))
  m + n * m + o * m   ≡⟨⟩
  suc n * m + o * m   ∎

------------------------------------------------------------------------
-- Lemma sketch (valid, 3 hole(s); lemmas *-distribʳ-+-lemma1)

*-distribʳ-+-lemma1 : (m : ℕ) → (n : ℕ) → (o : ℕ) → m + (n * m + o * m) ≡ m + n * m + o * m
*-distribʳ-+-lemma1 m n o = {!!}
*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ m zero    o = -- was: refl
  {!!}
*-distribʳ-+ m (suc n) o = begin-equality
  (suc n + o) * m     ≡⟨⟩
  m + (n + o) * m     ≡⟨ {!!} ⟩  -- was: cong (m +_) (*-distribʳ-+ m n o)
  m + (n * m + o * m) ≡⟨ *-distribʳ-+-lemma1 m n o ⟩
  m + n * m + o * m   ≡⟨⟩
  suc n * m + o * m   ∎
