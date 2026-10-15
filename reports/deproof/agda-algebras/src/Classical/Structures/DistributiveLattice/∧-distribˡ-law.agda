-- deproof: ∧-distribˡ-law
-- agda-algebras src/Classical/Structures/DistributiveLattice.lagda.md:123 @ c56c89b
-- An excerpt for reading: each part was checked by Agda in place, in its module.

------------------------------------------------------------------------
-- The library's proof

∧-distribˡ-law : ∀ x y z → x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)
∧-distribˡ-law x y z = begin
  x ∧ (y ∨ z)                   ≈⟨ ∧-cong refl (sym (interp-node-∨ (ℊ 1F) (ℊ 2F) {η})) ⟩
  x ∧ ⟦ y∨z ⟧ ⟨$⟩ η             ≈⟨ sym (interp-node-∧ (ℊ 0F) y∨z {η}) ⟩
  ⟦ lhsT ⟧ ⟨$⟩ η                ≈⟨ equations ∧-distribˡ η ⟩
  ⟦ rhsT ⟧ ⟨$⟩ η                ≈⟨ interp-node-∨ xy xz {η} ⟩
  ⟦ xy ⟧ ⟨$⟩ η ∨ ⟦ xz ⟧ ⟨$⟩ η   ≈⟨ ∨-cong (interp-node-∧ (ℊ 0F) (ℊ 1F) {η}) (interp-node-∧ (ℊ 0F) (ℊ 2F) {η}) ⟩
  (x ∧ y) ∨ (x ∧ z)             ∎
  where
  η : Fin 3 → 𝕌[ 𝑨 ]
  η = λ { 0F → x ; 1F → y ; 2F → z }
  y∨z xy xz lhsT rhsT : Term (Fin 3)
  y∨z  = node ∨-Op (pair (ℊ 1F) (ℊ 2F))
  xy   = node ∧-Op (pair (ℊ 0F) (ℊ 1F))
  xz   = node ∧-Op (pair (ℊ 0F) (ℊ 2F))
  lhsT = node ∧-Op (pair (ℊ 0F) y∨z)
  rhsT = node ∨-Op (pair xy xz)

------------------------------------------------------------------------
-- Its decomposition

-- ∧-distribˡ-law : ∀ x y z → x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)
-- 1 clause(s), 5 step(s), lemmas: ∧-cong, interp-node-∨, interp-node-∧, equations, ∨-cong
--
-- clause ∧-distribˡ-law x y z
--   goal: x ∧ (y ∨ z) ≈ x ∧ y ∨ x ∧ z
--   (where-block not taken apart)
--   1. x ∧ (y ∨ z) ≈ x ∧ ⟦ y∨z ⟧ ⟨$⟩ η
--        by ∧-cong refl (sym (interp-node-∨ (ℊ 1F) (ℊ 2F) {η}))   [∧-cong, interp-node-∨]
--   2. x ∧ ⟦ y∨z ⟧ ⟨$⟩ η ≈ ⟦ lhsT ⟧ ⟨$⟩ η
--        by sym (interp-node-∧ (ℊ 0F) y∨z {η})   [interp-node-∧]
--   3. ⟦ lhsT ⟧ ⟨$⟩ η ≈ ⟦ rhsT ⟧ ⟨$⟩ η
--        by equations ∧-distribˡ η   [equations]
--   4. ⟦ rhsT ⟧ ⟨$⟩ η ≈ ⟦ xy ⟧ ⟨$⟩ η ∨ ⟦ xz ⟧ ⟨$⟩ η
--        by interp-node-∨ xy xz {η}   [interp-node-∨]
--   5. ⟦ xy ⟧ ⟨$⟩ η ∨ ⟦ xz ⟧ ⟨$⟩ η ≈ (x ∧ y) ∨ (x ∧ z)
--        by ∨-cong (interp-node-∧ (ℊ 0F) (ℊ 1F) {η}) (interp-node-∧ (ℊ 0F) (ℊ 2F) {η})   [∨-cong, interp-node-∧]
--
-- lemmas used:
--   ∧-cong : (𝔻[ 𝑨 (distributiveLattice→lattice 𝑫) ] ≈ x₁) y₁ → (𝔻[ 𝑨 (distributiveLattice→lattice 𝑫) ] ≈ u) v → (𝔻[ 𝑨 (distributiveLattice→lattice 𝑫) ] ≈ x₁ ∧ u) (y₁ ∧ v)
--   interp-node-∨ : (s t : Term (Fin 3)) {η = η₁ : Fin 3 → 𝕌[ 𝑨 (distributiveLattice→lattice 𝑫) ]} → (𝔻[ 𝑨 (distributiveLattice→lattice 𝑫) ] ≈ (⟦ 𝑨 (distributiveLattice→lattice 𝑫) ⟧ (node ∨-Op (pair s t)) ⟨$⟩ η₁)) ((⟦ 𝑨 (distributiveLattice→lattice 𝑫) ⟧ s ⟨$⟩ η₁) ∨ (⟦ 𝑨 (distributiveLattice→lattice 𝑫) ⟧ t ⟨$⟩ η₁))
--   interp-node-∧ : (s t : Term (Fin 3)) {η = η₁ : Fin 3 → 𝕌[ 𝑨 (distributiveLattice→lattice 𝑫) ]} → (𝔻[ 𝑨 (distributiveLattice→lattice 𝑫) ] ≈ (⟦ 𝑨 (distributiveLattice→lattice 𝑫) ⟧ (node ∧-Op (pair s t)) ⟨$⟩ η₁)) ((⟦ 𝑨 (distributiveLattice→lattice 𝑫) ⟧ s ⟨$⟩ η₁) ∧ (⟦ 𝑨 (distributiveLattice→lattice 𝑫) ⟧ t ⟨$⟩ η₁))
--   equations : 𝑨 ⊨ᵈˡ Th-DistributiveLattice
--   ∨-cong : (𝔻[ 𝑨 (distributiveLattice→lattice 𝑫) ] ≈ x₁) y₁ → (𝔻[ 𝑨 (distributiveLattice→lattice 𝑫) ] ≈ u) v → (𝔻[ 𝑨 (distributiveLattice→lattice 𝑫) ] ≈ x₁ ∨ u) (y₁ ∨ v)

------------------------------------------------------------------------
-- Step sketch (valid, 5 hole(s))

∧-distribˡ-law : ∀ x y z → x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)
∧-distribˡ-law x y z = begin
  x ∧ (y ∨ z)                   ≈⟨ {!!} ⟩  -- was: ∧-cong refl (sym (interp-node-∨ (ℊ 1F) (ℊ 2F) {η}))
  x ∧ ⟦ y∨z ⟧ ⟨$⟩ η             ≈⟨ {!!} ⟩  -- was: sym (interp-node-∧ (ℊ 0F) y∨z {η})
  ⟦ lhsT ⟧ ⟨$⟩ η                ≈⟨ {!!} ⟩  -- was: equations ∧-distribˡ η
  ⟦ rhsT ⟧ ⟨$⟩ η                ≈⟨ {!!} ⟩  -- was: interp-node-∨ xy xz {η}
  ⟦ xy ⟧ ⟨$⟩ η ∨ ⟦ xz ⟧ ⟨$⟩ η   ≈⟨ {!!} ⟩  -- was: ∨-cong (interp-node-∧ (ℊ 0F) (ℊ 1F) {η}) (interp-node-∧ (ℊ 0F) (ℊ 2F) {η})
  (x ∧ y) ∨ (x ∧ z)             ∎
  where
  η : Fin 3 → 𝕌[ 𝑨 ]
  η = λ { 0F → x ; 1F → y ; 2F → z }
  y∨z xy xz lhsT rhsT : Term (Fin 3)
  y∨z  = node ∨-Op (pair (ℊ 1F) (ℊ 2F))
  xy   = node ∧-Op (pair (ℊ 0F) (ℊ 1F))
  xz   = node ∧-Op (pair (ℊ 0F) (ℊ 2F))
  lhsT = node ∧-Op (pair (ℊ 0F) y∨z)
  rhsT = node ∨-Op (pair xy xz)

------------------------------------------------------------------------
-- Lemma sketch (valid, 5 hole(s))

-- note: no step became a lemma (step 1: uses where-bound y∨z, η; step 2: uses where-bound lhsT, y∨z, η; step 3: uses where-bound lhsT, rhsT, η; step 4: uses where-bound rhsT, xy, xz, η; step 5: uses where-bound xy, xz, η)
∧-distribˡ-law : ∀ x y z → x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)
∧-distribˡ-law x y z = begin
  x ∧ (y ∨ z)                   ≈⟨ {!!} ⟩  -- was: ∧-cong refl (sym (interp-node-∨ (ℊ 1F) (ℊ 2F) {η}))
  x ∧ ⟦ y∨z ⟧ ⟨$⟩ η             ≈⟨ {!!} ⟩  -- was: sym (interp-node-∧ (ℊ 0F) y∨z {η})
  ⟦ lhsT ⟧ ⟨$⟩ η                ≈⟨ {!!} ⟩  -- was: equations ∧-distribˡ η
  ⟦ rhsT ⟧ ⟨$⟩ η                ≈⟨ {!!} ⟩  -- was: interp-node-∨ xy xz {η}
  ⟦ xy ⟧ ⟨$⟩ η ∨ ⟦ xz ⟧ ⟨$⟩ η   ≈⟨ {!!} ⟩  -- was: ∨-cong (interp-node-∧ (ℊ 0F) (ℊ 1F) {η}) (interp-node-∧ (ℊ 0F) (ℊ 2F) {η})
  (x ∧ y) ∨ (x ∧ z)             ∎
  where
  η : Fin 3 → 𝕌[ 𝑨 ]
  η = λ { 0F → x ; 1F → y ; 2F → z }
  y∨z xy xz lhsT rhsT : Term (Fin 3)
  y∨z  = node ∨-Op (pair (ℊ 1F) (ℊ 2F))
  xy   = node ∧-Op (pair (ℊ 0F) (ℊ 1F))
  xz   = node ∧-Op (pair (ℊ 0F) (ℊ 2F))
  lhsT = node ∧-Op (pair (ℊ 0F) y∨z)
  rhsT = node ∨-Op (pair xy xz)
