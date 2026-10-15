-- deproof: length-++
-- agda-stdlib src/Data/List/Properties.agda:129 @ 47beb93
-- An excerpt for reading: each part was checked by Agda in place, in its module.

------------------------------------------------------------------------
-- The library's proof

length-++ : ∀ (xs : List A) {ys} →
            length (xs ++ ys) ≡ length xs + length ys
length-++ []       = refl
length-++ (x ∷ xs) = cong suc (length-++ xs)

------------------------------------------------------------------------
-- Its decomposition

-- length-++ : ∀ (xs : List A) {ys} → length (xs ++ ys) ≡ length xs + length ys
-- 2 clause(s), 1 step(s) (+1 by computation or refl), lemmas: (none)
--
-- clause length-++ []
--   goal: length ([] ++ ys) ≡ length [] + length ys
--   1. length ([] ++ ys) ≡ length [] + length ys
--        by refl
--
-- clause length-++ (x ∷ xs)
--   goal: length ((x ∷ xs) ++ ys) ≡ length (x ∷ xs) + length ys
--   1. length ((x ∷ xs) ++ ys) ≡ length (x ∷ xs) + length ys
--        by cong suc (length-++ xs)   [IH]

------------------------------------------------------------------------
-- Step sketch (valid, 2 hole(s))

length-++ : ∀ (xs : List A) {ys} →
            length (xs ++ ys) ≡ length xs + length ys
length-++ []       = -- was: refl
  {!!}
length-++ (x ∷ xs) = -- was: cong suc (length-++ xs)
  {!!}

------------------------------------------------------------------------
-- Lemma sketch (valid, 2 hole(s))

-- note: no step became a lemma ([] 1: holds by computation; (x ∷ xs) 1: uses the induction hypothesis)
length-++ : ∀ (xs : List A) {ys} →
            length (xs ++ ys) ≡ length xs + length ys
length-++ []       = -- was: refl
  {!!}
length-++ (x ∷ xs) = -- was: cong suc (length-++ xs)
  {!!}
