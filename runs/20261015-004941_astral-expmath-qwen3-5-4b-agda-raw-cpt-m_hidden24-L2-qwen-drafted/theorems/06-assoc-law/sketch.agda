---
layout: default
file: "src/Classical/Structures/Group.lagda.md"
title: "Classical.Structures.Group module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Groups {#classical-structures-group}

This is the [Classical.Structures.Group][] module of the [Agda Universal Algebra Library][].

A **group** inhabits the Σ-typed structure `Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Group` over
`Sig-Group`.  Group is the first structure whose signature grows over its
predecessor's by a *unary* symbol (`Sig-Group` adds `⁻¹-Op` to `Sig-Monoid`); its
forgetful projection `group→monoid` is therefore a reduct that drops `⁻¹-Op`,
discharging the three monoid equations on the reduct by the curried-law pivot of
the `monoid→semigroup` of [`Classical.Structures.Monoid`][] (here extended from one
law to three, the two identity laws additionally bridging the nullary `ε-Op` node).

This module follows the [Monoid][Classical.Structures.Monoid] template, adding the
following to it.

+  **Direct curried accessors for all three operations**.  `Group-Op` defines
   `_∙_ = Curry₂ (∙-Op ^ 𝑨)`, `ε = Curry₀ (ε-Op ^ 𝑨)`, and
   `_⁻¹ = Curry₁ (⁻¹-Op ^ 𝑨)` directly over `Sig-Group`, never inheriting through the
   reduct, for the reason Monoid gives: keeping the accessors direct keeps every
   downstream `refl` off the reduct's position-map reduction.
+  **A unary node-bridge**.  Alongside the binary `interp-node-∙` and nullary
   `interp-node-ε`, `Group-Op` has `interp-node-⁻¹` for the unary `⁻¹-Op`, a
   one-liner delegating to `interp-cong` exactly as the other two do.
+  **Two inverse laws**.  `invˡ-law` and `invʳ-law` join the three monoid laws in
   `Group-Op`; they are the only laws not consumed by the forgetful (which lands in
   `Monoid`, below the inverse structure), so they live in `Group-Op` rather than in
   the standalone curried-law block.

```agda
{-# OPTIONS --cubical-compatible --exact-split #-}

module Classical.Structures.Group where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -------------------------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; cong ; cong₂ ; setoid )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Func renaming ( to to _⟨$⟩_ ; cong to ≈cong )

-- Imports from the Agda Universal Algebra Library -----------------------------------------------
open import Classical.Operations            using  ( pair ; Curry₂ ; Curry₁ ; Curry₀ )
open import Classical.Signatures.Monoid     using  ( Sig-Monoid ; Op-Monoid )
                                            renaming ( ∙-Op to ∙-Opᵐᵒ ; ε-Op to ε-Opᵐᵒ )
open import Classical.Signatures.Group      using  ( Sig-Group ; Op-Group ; ∙-Op ; ε-Op ; ⁻¹-Op ; ar-Group)
open import Classical.Structures.Interpret  using  ( interp-cong )
open import Setoid.Algebras.Reduct          using  ( reductBy )
open import Classical.Structures.Monoid     using  ( Monoid ; _⊨ᵐᵒ_ )
open import Classical.Theories.Group        using  ( Eq-Group ; Th-Group
                                                   ; assoc ; idˡ ; idʳ ; invˡ ; invʳ )
open import Classical.Theories.Monoid       using  ( Th-Monoid )
                                            renaming ( assoc to assocᵐ ; idˡ to idˡᵐ ; idʳ to idʳᵐ )
open import Overture.Terms                  using  ( Term ; ℊ ; node )
open import Overture.Signatures             using  ( ArityOf ; OperationSymbolsOf )
open import Setoid.Algebras.Basic           using  ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms                    using  ( module Environment )

open import Setoid.Varieties.EquationalLogic {𝑆 = Sig-Group} using ( _⊧_≈_ )

private variable α ρ : Level
```

#### The local satisfaction predicate

```agda
infix 4 _⊨ᵍᵖ_
_⊨ᵍᵖ_ : (𝑨 : Algebra α ρ) (ℰ : Eq-Group → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ᵍᵖ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)
```

#### The type of groups

```agda
Group : (α ρ : Level) → Type (suc α ⊔ suc ρ)
Group α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ᵍᵖ Th-Group
```

#### The reduct to monoids

The container morphism `Sig-Monoid ⟹ Sig-Group` sends the monoid's `∙-Opᵐᵒ` and
`ε-Opᵐᵒ` to the group's `∙-Op` and `ε-Op`; the position maps are the identity.
`group→monoidAlg` is the induced reduct of the underlying algebra.

```agda
mo-incl : Op-Monoid → Op-Group
mo-incl ∙-Opᵐᵒ = ∙-Op
mo-incl ε-Opᵐᵒ = ε-Op

mo-κ : (o : OperationSymbolsOf Sig-Monoid)
  → ArityOf Sig-Group (mo-incl o) → ArityOf Sig-Monoid o
mo-κ ∙-Opᵐᵒ = λ z → z
mo-κ ε-Opᵐᵒ = λ z → z

group→monoidAlg : Group α ρ → Algebra {𝑆 = Sig-Monoid} α ρ
group→monoidAlg 𝑮 = reductBy mo-incl mo-κ (𝑮 .proj₁)
```

#### Curried associativity, standalone

`gp-assoc` proves `(x ∙ y) ∙ z ≈ x ∙ (y ∙ z)` for the group's own `∙`, a verbatim
port of `Monoid-Op.mn-assoc` to `Sig-Group`.  It is standalone, above the forgetful,
so both `Group-Op.assoc-law` and the `group→monoid` discharge consume one proof.

```agda
module _ (𝑮 : Group α ρ) where
  private 𝑨 = proj₁ 𝑮
  open Setoid 𝔻[ 𝑨 ] using (_≈_) renaming (sym to ≈sym ; refl to ≈refl)
  open Environment 𝑨 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑨 ]

  private
    infixl 7 _∙_
    _∙_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
    _∙_ = Curry₂ (∙-Op ^ 𝑨)

```

#### The `Group-Op` module

```agda
module Group-Op {α ρ : Level} (𝑮 : Group α ρ) where
  private 𝑨 = proj₁ 𝑮
  open Setoid 𝔻[ 𝑨 ] using (_≈_) renaming (trans to ≈trans; sym to ≈sym; refl to ≈refl)
  open SetoidReasoning 𝔻[ 𝑨 ]
  open Environment 𝑨 using ( ⟦_⟧ )

  infixl 7 _∙_
  _∙_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
  _∙_ = Curry₂ (∙-Op ^ 𝑨)

  ε : 𝕌[ 𝑨 ]
  ε = Curry₀ (ε-Op ^ 𝑨)

  infix 8 _⁻¹
  _⁻¹ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
  _⁻¹ = Curry₁ (⁻¹-Op ^ 𝑨)

  equations : 𝑨 ⊨ᵍᵖ Th-Group
  equations = proj₂ 𝑮

  ∙-cong : ∀ {x y u v} → x ≈ y → u ≈ v → x ∙ u ≈ y ∙ v
  ∙-cong x≈y u≈v = interp-cong 𝑨 ∙-Op (λ { 0F → x≈y ; 1F → u≈v })

  ⁻¹-cong : ∀ {x y} → x ≈ y → x ⁻¹ ≈ y ⁻¹
  ⁻¹-cong x≈y = interp-cong 𝑨 ⁻¹-Op (λ { 0F → x≈y })

  interp-node-∙ : (s t : Term (Fin 3)) {η : Fin 3 → 𝕌[ 𝑨 ]}
    → ⟦ node ∙-Op (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ∙ ⟦ t ⟧ ⟨$⟩ η
  interp-node-∙ s t = interp-cong 𝑨 ∙-Op (λ { 0F → ≈refl ; 1F → ≈refl })

  interp-node-ε : {η : Fin 3 → 𝕌[ 𝑨 ]} → ⟦ node ε-Op (λ ()) ⟧ ⟨$⟩ η ≈ ε
  interp-node-ε = interp-cong 𝑨 ε-Op (λ ())

  interp-node-⁻¹ : (s : Term (Fin 3)) {η : Fin 3 → 𝕌[ 𝑨 ]}
    → ⟦ node ⁻¹-Op (λ _ → s) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ⁻¹
  interp-node-⁻¹ s = interp-cong 𝑨 ⁻¹-Op (λ { 0F → ≈refl })

  -- dsp: lemmas
  -- dsp: end of lemmas
  assoc-law : ∀ x y z → x ∙ y ∙ z ≈ x ∙ (y ∙ z)
  assoc-law x y z = {!!}
                where open SetoidReasoning 𝔻[ 𝑨 ]
```
