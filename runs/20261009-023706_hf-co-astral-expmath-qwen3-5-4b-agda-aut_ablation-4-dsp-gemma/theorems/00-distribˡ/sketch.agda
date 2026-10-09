------------------------------------------------------------------------
-- The Agda standard library
--
-- The non-commutative analogue of Nagata's construction of
-- the "idealization of a module", (Local Rings, 1962; Wiley)
-- defined here on R-R-*bi*modules M over a ring R, as used in
-- "Forward- or reverse-mode automatic differentiation: What's the difference?"
-- (Van den Berg, Schrijvers, McKinna, Vandenbroucke;
-- Science of Computer Programming, Vol. 234, January 2024
-- https://doi.org/10.1016/j.scico.2023.103010)
--
-- The construction N =def R ⋉ M , for which there is unfortunately
-- no consistent notation in the literature, consists of:
-- * carrier: pairs |R| × |M|
-- * with additive structure that of the direct sum R ⊕ M _of modules_
-- * but with multiplication _*_ such that M forms an _ideal_ of N
-- * moreover satisfying 'm * m ≈ 0' for every m ∈ M ⊆ N
--
-- The fundamental lemma (proved here) is that N, in fact, defines a Ring:
-- this ring is essentially the 'ring of dual numbers' construction R[M]
-- (Clifford, 1874; generalised!) for an ideal M, and thus the synthetic/algebraic
-- analogue of the tangent space of M (considered as a 'vector space' over R)
-- in differential geometry, hence its application to Automatic Differentiation.
--
-- Nagata's more fundamental insight (not yet shown here) is that
-- the lattice of R-submodules of M is in order-isomorphism with
-- the lattice of _ideals_ of R ⋉ M , and hence that the study of
-- modules can be reduced to that of ideals of a ring, and vice versa.
--
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Algebra.Bundles using (AbelianGroup; Ring)
open import Algebra.Module.Bundles using (Bimodule)

module Algebra.Module.Construct.Idealization
  {r ℓr m ℓm} (ring : Ring r ℓr) (bimodule : Bimodule ring ring m ℓm) where

open import Algebra.Core using (Op₂)
import Algebra.Consequences.Setoid as Consequences using (comm∧assoc⇒middleFour)
import Algebra.Definitions as Definitions
  using (Congruent₂; _DistributesOverˡ_; _DistributesOverʳ_; _DistributesOver_
        ; LeftIdentity; RightIdentity; Identity; Associative)
import Algebra.Module.Construct.DirectProduct as DirectProduct using (bimodule)
import Algebra.Module.Construct.TensorUnit as TensorUnit using (bimodule)
open import Algebra.Structures using (IsAbelianGroup; IsRing)
open import Data.Product.Base using (_,_; ∃-syntax)
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using  (Setoid)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

------------------------------------------------------------------------
-- Definitions

private
  open module R = Ring ring
    using ()
    renaming (Carrier to R)

  open module M = Bimodule bimodule
    renaming (Carrierᴹ to M)

  +ᴹ-middleFour = Consequences.comm∧assoc⇒middleFour ≈ᴹ-setoid +ᴹ-cong +ᴹ-comm +ᴹ-assoc

  open module N = Bimodule (DirectProduct.bimodule TensorUnit.bimodule bimodule)
    using ()
    renaming ( Carrierᴹ to N
             ; _≈ᴹ_ to _≈_
             ; _+ᴹ_ to _+_
             ; 0ᴹ to 0#
             ; -ᴹ_ to -_
             ; +ᴹ-isAbelianGroup to +-isAbelianGroup
             )

open AbelianGroup M.+ᴹ-abelianGroup hiding (_≈_)
open ≈-Reasoning ≈ᴹ-setoid
open Definitions _≈_

-- Injections ι from the components of the direct sum
-- ιᴹ in fact exhibits M as an _ideal_ of R ⋉ M (see below)
ιᴿ : R → N
ιᴿ r = r , 0ᴹ

ιᴹ : M → N
ιᴹ m = R.0# , m

-- Multiplicative unit

1# : N
1# = ιᴿ R.1#

-- Multiplication

infixl 7 _*_

_*_ : Op₂ N
(r₁ , m₁) * (r₂ , m₂) = r₁ R.* r₂ , r₁ *ₗ m₂ +ᴹ m₁ *ᵣ r₂

-- Properties: because we work in the direct sum, every proof has
-- * an 'R'-component, which inherits directly from R, and
-- * an 'M'-component, where the work happens

*-cong : Congruent₂ _*_
*-cong (r₁ , m₁) (r₂ , m₂) = R.*-cong r₁ r₂ , +ᴹ-cong (*ₗ-cong r₁ m₂) (*ᵣ-cong m₁ r₂)

*-identityˡ : LeftIdentity 1# _*_
*-identityˡ (r , m) = R.*-identityˡ r , (begin
  R.1# *ₗ m +ᴹ 0ᴹ *ᵣ r ≈⟨ +ᴹ-cong (*ₗ-identityˡ m) (*ᵣ-zeroˡ r) ⟩
  m +ᴹ 0ᴹ              ≈⟨ +ᴹ-identityʳ m ⟩
  m                    ∎)

*-identityʳ : RightIdentity 1# _*_
*-identityʳ (r , m) = R.*-identityʳ r , (begin
  r *ₗ 0ᴹ +ᴹ m *ᵣ R.1# ≈⟨ +ᴹ-cong (*ₗ-zeroʳ r) (*ᵣ-identityʳ m) ⟩
  0ᴹ +ᴹ m              ≈⟨ +ᴹ-identityˡ m ⟩
  m                    ∎)

*-identity : Identity 1# _*_
*-identity = *-identityˡ , *-identityʳ

*-assoc : Associative _*_
*-assoc (r₁ , m₁) (r₂ , m₂) (r₃ , m₃) = R.*-assoc r₁ r₂ r₃ , (begin
  (r₁ R.* r₂) *ₗ m₃ +ᴹ (r₁ *ₗ m₂ +ᴹ m₁ *ᵣ r₂) *ᵣ r₃
    ≈⟨ +ᴹ-cong (*ₗ-assoc r₁ r₂ m₃) (*ᵣ-distribʳ r₃ (r₁ *ₗ m₂) (m₁ *ᵣ r₂)) ⟩
  r₁ *ₗ (r₂ *ₗ m₃) +ᴹ ((r₁ *ₗ m₂) *ᵣ r₃ +ᴹ (m₁ *ᵣ r₂) *ᵣ r₃)
    ≈⟨ +ᴹ-congˡ (+ᴹ-congʳ (*ₗ-*ᵣ-assoc r₁ m₂ r₃)) ⟩
  r₁ *ₗ (r₂ *ₗ m₃) +ᴹ (r₁ *ₗ (m₂ *ᵣ r₃) +ᴹ (m₁ *ᵣ r₂) *ᵣ r₃)
    ≈⟨ +ᴹ-assoc (r₁ *ₗ (r₂ *ₗ m₃)) (r₁ *ₗ (m₂ *ᵣ r₃)) ((m₁ *ᵣ r₂) *ᵣ r₃) ⟨
  (r₁ *ₗ (r₂ *ₗ m₃) +ᴹ r₁ *ₗ (m₂ *ᵣ r₃)) +ᴹ (m₁ *ᵣ r₂) *ᵣ r₃
    ≈⟨ +ᴹ-cong (≈ᴹ-sym (*ₗ-distribˡ r₁ (r₂ *ₗ m₃) (m₂ *ᵣ r₃))) (*ᵣ-assoc m₁ r₂ r₃) ⟩
  r₁ *ₗ (r₂ *ₗ m₃ +ᴹ m₂ *ᵣ r₃) +ᴹ m₁ *ᵣ (r₂ R.* r₃) ∎)

-- dsp: lemmas
-- dsp: end of lemmas
distribˡ : _*_ DistributesOverˡ _+_
distribˡ (r₁ , m₁) (r₂ , m₂) (r₃ , m₃) = {!!} , {!!}
