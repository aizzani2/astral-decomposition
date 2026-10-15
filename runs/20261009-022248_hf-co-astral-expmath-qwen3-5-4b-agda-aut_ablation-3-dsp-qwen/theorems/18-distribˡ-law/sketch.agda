---
layout: default
file: "src/Classical/Structures/DistributiveLattice.lagda.md"
title: "Classical.Structures.DistributiveLattice module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Distributive lattices {#classical-structures-distributivelattice}

This is the [Classical.Structures.DistributiveLattice][] module of the [Agda Universal Algebra Library][].

A **distributive lattice** inhabits `Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-DistributiveLattice`
over the *same* `Sig-Lattice` signature as [`Lattice`][Classical.Structures.Lattice].
It is an *equation-only* extension of `Lattice`: the forgetful
`distributiveLattice→lattice` is a pure theory-reindex (the two distributivity
equations are dropped, the remaining eight map across definitionally), and
`DistributiveLattice-Op` inherits `_∧_`, `_∨_`, both congruences, the node bridges,
and all eight lattice laws through it.  This is the two-operation analogue of how
[`CommutativeMonoid`][Classical.Structures.CommutativeMonoid] extends `Monoid`.

On top of the inherited laws this module adds four distributivity laws in curried
form: the two *left* laws `∧-distribˡ-law` and `∨-distribˡ-law` come straight from
the theory's two witnesses (the proof shape is `Ring`'s `rg-distribˡ`), and the two
*right* laws `∧-distribʳ-law` and `∨-distribʳ-law` are derived from them by
commutativity.  All four are what the bundle bridge feeds to the standard library's
`IsDistributiveLattice`, whose `∨-distrib-∧` and `∧-distrib-∨` fields each pair a
left and a right law.

```agda
{-# OPTIONS --cubical-compatible --exact-split #-}

module Classical.Structures.DistributiveLattice where

open import Agda.Primitive                using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Fin.Base                 using ( Fin )
open import Data.Fin.Patterns             using ( 0F ; 1F ; 2F )
open import Data.Product                  using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                      using ( Func )
open import Level                         using ( Level ; _⊔_ ; suc )
open import Relation.Binary               using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Operations          using  ( pair )
open import Classical.Signatures.Lattice  using  ( Sig-Lattice ; ∧-Op ; ∨-Op )
open import Classical.Structures.Lattice  using  ( Lattice ; module Lattice-Op
                                                 ; opsToBareLattice )
open import Classical.Theories.Lattice    using  ()
  renaming  ( ∧-assoc to ∧-assocˡᵃ ; ∧-comm to ∧-commˡᵃ ; ∧-idem to ∧-idemˡᵃ
            ; ∨-assoc to ∨-assocˡᵃ ; ∨-comm to ∨-commˡᵃ ; ∨-idem to ∨-idemˡᵃ
            ; absorbˡ to absorbˡˡᵃ ; absorbʳ to absorbʳˡᵃ )

open import Classical.Theories.DistributiveLattice
  using  ( Eq-DistributiveLattice ; Th-DistributiveLattice ; ∧-assoc ; ∧-comm ; ∧-idem
         ; ∨-assoc ; ∨-comm ; ∨-idem ; absorbˡ ; absorbʳ ; ∧-distribˡ ; ∨-distribˡ )

open import Overture.Terms {𝑆 = Sig-Lattice} using ( Term ; ℊ ; node )
open import Setoid.Algebras.Basic {𝑆 = Sig-Lattice} using ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms using ( module Environment )
open import Setoid.Varieties.EquationalLogic {𝑆 = Sig-Lattice} using ( _⊧_≈_ )

private variable α ρ : Level
```

#### The satisfaction predicate and the type of distributive lattices {#the-type}

```agda
infix 4 _⊨ᵈˡ_
_⊨ᵈˡ_ : (𝑨 : Algebra α ρ) (ℰ : Eq-DistributiveLattice → Term (Fin 3) × Term (Fin 3))
  → Type (α ⊔ ρ)

𝑨 ⊨ᵈˡ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)

DistributiveLattice : (α ρ : Level) → Type (suc α ⊔ suc ρ)
DistributiveLattice α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ᵈˡ Th-DistributiveLattice
```

#### The forgetful projection to lattices {#forgetful-to-lattice}

The eight lattice equations are dropped from `Th-DistributiveLattice` to `Th-Lattice`.
Because each shared equation is built by the *same* `Classical.Equations` builder on
both sides, `Th-Lattice c` and `Th-DistributiveLattice c` are definitionally equal,
so the witnesses transport with no work — the two distributivity equations are simply
not requested.

```agda
distributiveLattice→lattice : DistributiveLattice α ρ → Lattice α ρ
distributiveLattice→lattice (𝑨 , mod) = 𝑨 ,
  λ { ∧-assocˡᵃ → mod ∧-assoc ; ∧-commˡᵃ → mod ∧-comm ; ∧-idemˡᵃ → mod ∧-idem
    ; ∨-assocˡᵃ → mod ∨-assoc ; ∨-commˡᵃ → mod ∨-comm ; ∨-idemˡᵃ → mod ∨-idem
    ; absorbˡˡᵃ → mod absorbˡ ; absorbʳˡᵃ → mod absorbʳ }
```

#### The `DistributiveLattice-Op` module {#distributivelattice-op}

`DistributiveLattice-Op` re-exports the meet/join operations, congruences, node
bridges, and eight lattice laws from the inherited `Lattice-Op`, and adds the four
distributivity laws.

```agda
module DistributiveLattice-Op {α ρ : Level} (𝑫 : DistributiveLattice α ρ) where
  private 𝑨 = proj₁ 𝑫
  open Setoid 𝔻[ 𝑨 ]
  open Environment 𝑨 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑨 ]

  open Lattice-Op (distributiveLattice→lattice 𝑫) public
    using  ( _∧_ ; ∧-cong ; interp-node-∧ ; ∧-assoc-law ; ∧-comm-law ; ∧-idem-law
           ; _∨_ ; ∨-cong ; interp-node-∨ ; ∨-assoc-law ; ∨-comm-law ; ∨-idem-law
           ; absorbˡ-law ; absorbʳ-law )

  equations : 𝑨 ⊨ᵈˡ Th-DistributiveLattice
  equations = proj₂ 𝑫

  -- x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)   (meet distributes over join, on the left)
  -- dsp: lemmas
  postulate
    meetJoinDistribLem : ∀ x y z → (x ∧ (y ∨ z)) ≈ ((x ∧ y) ∨ (x ∧ z))

  -- dsp: end of lemmas
  ∧-distribˡ-law : ∀ x y z → x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)
  ∧-distribˡ-law = meetJoinDistribLem
```
