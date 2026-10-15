------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties for distributive lattice
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Relation.Binary.Lattice

module Relation.Binary.Lattice.Properties.DistributiveLattice
  {c ℓ₁ ℓ₂} (L : DistributiveLattice c ℓ₁ ℓ₂) where

open import Data.Product.Base using (_,_)
open import Relation.Binary.Bundles using (Setoid)

open DistributiveLattice L hiding (refl)

open import Algebra.Definitions _≈_
  using (Zero; RightZero; LeftZero
        ; _DistributesOverʳ_; _DistributesOverˡ_; _DistributesOver_)
open import Relation.Binary.Reasoning.Setoid setoid
open import Relation.Binary.Lattice.Properties.Lattice lattice
  using (∧-absorbs-∨; ∨-absorbs-∧ )
open import Relation.Binary.Lattice.Properties.MeetSemilattice meetSemilattice
  using (∧-comm; ∧-cong)
open import Relation.Binary.Lattice.Properties.JoinSemilattice joinSemilattice
  using (∨-comm; ∨-cong; ∨-assoc)

open Setoid setoid

∧-distribʳ-∨ : _∧_ DistributesOverʳ _∨_
∧-distribʳ-∨ x y z = begin
  (y ∨ z) ∧ x    ≈⟨ ∧-comm _ _ ⟩
  x ∧ (y ∨ z)    ≈⟨ ∧-distribˡ-∨ x y z ⟩
  x ∧ y ∨ x ∧ z  ≈⟨ ∨-cong (∧-comm _ _) (∧-comm _ _) ⟩
  y ∧ x ∨ z ∧ x  ∎

-- dsp: lemmas
-- dsp: end of lemmas
∧-distrib-∨ : _∧_ DistributesOver _∨_
-- No informal proof steps were provided.
∧-distrib-∨ = ((λ x y z → Setoid.trans setoid (∧-comm x (y ∨ z)) (Setoid.trans setoid (∧-distribʳ-∨ x y z) (∨-cong (∧-comm y x) (∧-comm z x)))) , ∧-distribʳ-∨)
