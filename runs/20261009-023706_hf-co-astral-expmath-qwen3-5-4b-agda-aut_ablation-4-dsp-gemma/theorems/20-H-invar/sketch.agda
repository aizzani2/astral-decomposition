---
layout: default
title : "Base.Varieties.Properties module (The Agda Universal Algebra Library)"
date : "2021-06-24"
author: "agda-algebras development team"
---

### <a id="properties-of-the-models-relation">Properties of the models relation</a>

We prove some closure and invariance properties of the relation `⊧`.  In particular,
we prove the following facts (which we use later in our proof of Birkhoff's HSP Theorem).

*  [Algebraic invariance](#algebraic-invariance). `⊧` is an *algebraic invariant*
   (stable under isomorphism).

*  [Subalgebraic invariance](#subalgebraic-invariance). Identities modeled by a
   class of algebras are also modeled by all subalgebras of algebras in the class.

*  [Product invariance](#product-invariance). Identities modeled by a class of
   algebras are also modeled by all products of algebras in the class.


```agda


{-# OPTIONS --cubical-compatible --exact-split #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Legacy.Base.Varieties.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ-syntax ; _×_ )
                            renaming ( proj₁ to fst ; proj₂ to snd )
open import Function        using ( _∘_ )
open import Level           using ( Level ; _⊔_ )
open import Relation.Unary  using ( Pred ; _∈_ ; _⊆_ ; ⋂ )
open import Axiom.Extensionality.Propositional
                            using () renaming ( Extensionality to funext )
open import Relation.Binary.PropositionalEquality
                            using ( _≡_ ; refl ; module ≡-Reasoning ; cong )

-- Imports from the Agda Universal Algebra Library -------------------------------
open import Overture                     using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Legacy.Base.Functions               using ( IsInjective ; ∘-injective )
open import Legacy.Base.Equality                using ( SwellDef ; DFunExt )
open import Legacy.Base.Algebras       {𝑆 = 𝑆}  using ( Algebra ; Lift-Alg ; ov ; ⨅ )
open import Legacy.Base.Homomorphisms  {𝑆 = 𝑆}  using ( hom ; ∘-hom ; _≅_ ; mkiso )
                                         using ( Lift-≅ ; ≅-sym ; ≅-trans )
open import Legacy.Base.Terms          {𝑆 = 𝑆}  using ( Term ; 𝑻 ; lift-hom ; _⟦_⟧ )
                                         using ( comm-hom-term ; interp-prod )
                                         using ( term-agreement )
open import Legacy.Base.Subalgebras    {𝑆 = 𝑆}  using ( _≤_ ; SubalgebraOfClass )
                                         using ( iso→injective )
open import Legacy.Base.Varieties.EquationalLogic
                                {𝑆 = 𝑆}  using ( _⊧_≈_ ; _⊫_≈_ )
```



#### <a id="algebraic-invariance-of-models">Algebraic invariance of ⊧</a>

The binary relation ⊧ would be practically useless if it were not an *algebraic
invariant* (invariant under isomorphism).


```agda


open Term
open ≡-Reasoning
open _≅_

module _  (wd : SwellDef){α β χ : Level}{X : Type χ}{𝑨 : Algebra α}
          (𝑩 : Algebra β)(p q : Term X) where

 ⊧-I-invar : 𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q

 ⊧-I-invar Apq (mkiso f g f∼g g∼f) x =
  (𝑩 ⟦ p ⟧) x                       ≡⟨ i p ⟩
  (𝑩 ⟦ p ⟧) ((∣ f ∣ ∘ ∣ g ∣) ∘ x)   ≡⟨ (ii p) ⁻¹ ⟩
  ∣ f ∣ ((𝑨 ⟦ p ⟧) (∣ g ∣ ∘ x))     ≡⟨ cong ∣ f ∣ (Apq (∣ g ∣ ∘ x))  ⟩
  ∣ f ∣ ((𝑨 ⟦ q ⟧) (∣ g ∣ ∘ x))     ≡⟨ ii q ⟩
  (𝑩 ⟦ q ⟧) ((∣ f ∣ ∘ ∣ g ∣) ∘  x)  ≡⟨ (i q)⁻¹ ⟩
  (𝑩 ⟦ q ⟧) x                       ∎
  where
  i : ∀ t → (𝑩 ⟦ t ⟧) x ≡ (𝑩 ⟦ t ⟧) λ x₁ → ∣ f ∣ (∣ g ∣ (x x₁))
  i t = wd χ β (𝑩 ⟦ t ⟧) x (∣ f ∣ ∘ ∣ g ∣ ∘ x) λ i → ( f∼g (x i))⁻¹

  ii :  ∀ t
   →    ∣ f ∣((𝑨 ⟦ t ⟧) λ x₁ → ∣ g ∣(x x₁)) ≡ (𝑩 ⟦ t ⟧) λ x₁ → ∣ f ∣(∣ g ∣(x x₁))
  ii t = comm-hom-term (wd 𝓥 β) 𝑩 f t (∣ g ∣ ∘ x)
```



In the above proof we showed `𝑩 ⊧ p ≈ q` by showing that `𝑩 ⟦ p ⟧ ≡ 𝑩 ⟦ q ⟧` holds
*extensionally*, that is, `∀ x, 𝑩 ⟦ p ⟧ x ≡ 𝑩 ⟦q ⟧ x`.

#### <a id="lift-invariance-of-models">Lift-invariance of ⊧</a>
The `⊧` relation is also invariant under the algebraic lift and lower operations.


```agda


module _ (wd : SwellDef){α β χ : Level}{X : Type χ}{𝑨 : Algebra α} where

 ⊧-Lift-invar : (p q : Term X) → 𝑨 ⊧ p ≈ q → Lift-Alg 𝑨 β ⊧ p ≈ q
 ⊧-Lift-invar p q Apq = ⊧-I-invar wd (Lift-Alg 𝑨 _) p q Apq Lift-≅

 ⊧-lower-invar : (p q : Term X) → Lift-Alg 𝑨 β ⊧ p ≈ q  →  𝑨 ⊧ p ≈ q
 ⊧-lower-invar p q lApq = ⊧-I-invar wd 𝑨 p q lApq (≅-sym Lift-≅)
```




#### <a id="subalgebraic-invariance">Subalgebraic invariance of ⊧</a>

Identities modeled by an algebra `𝑨` are also modeled by every subalgebra of `𝑨`,
which fact can be formalized as follows.


```agda


module _ (wd : SwellDef){χ : Level}{𝓤 𝓦 : Level}{X : Type χ} where

 ⊧-S-invar : {𝑨 : Algebra 𝓤}(𝑩 : Algebra 𝓦){p q : Term X}
  →          𝑨 ⊧ p ≈ q  →  𝑩 ≤ 𝑨  →  𝑩 ⊧ p ≈ q
 ⊧-S-invar {𝑨} 𝑩 {p}{q} Apq B≤A b = (∥ B≤A ∥) (ξ b)
  where
  h : hom 𝑩 𝑨
  h = ∣ B≤A ∣

  ξ : ∀ b → ∣ h ∣ ((𝑩 ⟦ p ⟧) b) ≡ ∣ h ∣ ((𝑩 ⟦ q ⟧) b)
  ξ b =  ∣ h ∣((𝑩 ⟦ p ⟧) b)    ≡⟨ comm-hom-term (wd 𝓥 𝓤) 𝑨 h p b ⟩
         (𝑨 ⟦ p ⟧)(∣ h ∣ ∘ b)  ≡⟨ Apq (∣ h ∣ ∘ b) ⟩
         (𝑨 ⟦ q ⟧)(∣ h ∣ ∘ b)  ≡⟨ (comm-hom-term (wd 𝓥 𝓤) 𝑨 h q b)⁻¹ ⟩
         ∣ h ∣((𝑩 ⟦ q ⟧) b)    ∎
```


Next, identities modeled by a class of algebras is also modeled by all subalgebras
of the class.  In other terms, every term equation `p ≈ q` that is satisfied by all
`𝑨 ∈ 𝒦` is also satisfied by every subalgebra of a member of `𝒦`.

 
```agda


 ⊧-S-class-invar :  {𝒦 : Pred (Algebra 𝓤)(ov 𝓤)}(p q : Term X)
  →                 𝒦 ⊫ p ≈ q → (𝑩 : SubalgebraOfClass 𝒦) → ∣ 𝑩 ∣ ⊧ p ≈ q

 ⊧-S-class-invar p q Kpq (𝑩 , 𝑨 , SA , (ka , B≅SA)) =
  ⊧-S-invar 𝑩 {p}{q}((Kpq ka)) (h , hinj)
   where
   h : hom 𝑩 𝑨
   h = ∘-hom 𝑩 𝑨 (to B≅SA) ∣ snd SA ∣
   hinj : IsInjective ∣ h ∣
   hinj = ∘-injective (iso→injective B≅SA) ∥ snd SA ∥
```



#### <a id="product-invariance-of-models">Product invariance of ⊧</a>

An identity satisfied by all algebras in an indexed collection is also satisfied
by the product of algebras in that collection.


```agda


module _  (fe : DFunExt)(wd : SwellDef)
          {α β χ : Level}{I : Type β}
          (𝒜 : I → Algebra α){X : Type χ} where

 ⊧-P-invar : (p q : Term X) → (∀ i → 𝒜 i ⊧ p ≈ q) → ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-invar p q 𝒜pq a = goal
  where
  -- This is where function extensionality is used.
  ξ : (λ i → (𝒜 i ⟦ p ⟧) (λ x → (a x) i)) ≡ (λ i → (𝒜 i ⟦ q ⟧)  (λ x → (a x) i))
  ξ = fe β α λ i → 𝒜pq i (λ x → (a x) i)

  goal : (⨅ 𝒜 ⟦ p ⟧) a  ≡  (⨅ 𝒜 ⟦ q ⟧) a
  goal =  (⨅ 𝒜 ⟦ p ⟧) a                      ≡⟨ interp-prod (wd 𝓥 (α ⊔ β)) p 𝒜 a ⟩
          (λ i → (𝒜 i ⟦ p ⟧)(λ x → (a x)i))  ≡⟨ ξ ⟩
          (λ i → (𝒜 i ⟦ q ⟧)(λ x → (a x)i))  ≡⟨ (interp-prod (wd 𝓥 (α ⊔ β)) q 𝒜 a)⁻¹ ⟩
          (⨅ 𝒜 ⟦ q ⟧) a                      ∎
```


An identity satisfied by all algebras in a class is also satisfied by the product
of algebras in the class.


```agda


 ⊧-P-class-invar :  (𝒦 : Pred (Algebra α)(ov α)){p q : Term X}
  →                 𝒦 ⊫ p ≈ q → (∀ i → 𝒜 i ∈ 𝒦) → ⨅ 𝒜 ⊧ p ≈ q

 ⊧-P-class-invar 𝒦 {p}{q}σ K𝒜 = ⊧-P-invar p q λ i → σ (K𝒜 i)
```


Another fact that will turn out to be useful is that a product of a collection of
algebras models ``p ≈ q`` if the lift of each algebra in the collection models ``p ≈ q``.


```agda


 ⊧-P-lift-invar : (p q : Term X) → (∀ i → Lift-Alg (𝒜 i) β ⊧ p ≈ q)  →  ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-lift-invar p q α = ⊧-P-invar p q Aipq
  where
  Aipq : ∀ i → (𝒜 i) ⊧ p ≈ q
  Aipq i = ⊧-lower-invar wd p q (α i)
```


#### <a id="homomorphisc-invariance-of-models">Homomorphic invariance of ⊧</a>

If an algebra `𝑨` models an identity `p ≈ q`, then the pair `(p , q)`
belongs to the kernel of every homomorphism `φ : hom (𝑻 X) 𝑨` from the term
algebra to `𝑨`; that is, every homomorphism from `𝑻 X` to `𝑨` maps `p` and
`q` to the same element of `𝑨`.

 
```agda


module _ (wd : SwellDef){α χ : Level}{X : Type χ}{𝑨 : Algebra α} where

 -- dsp: lemmas
 -- dsp: end of lemmas
 ⊧-H-invar : {p q : Term X}(φ : hom (𝑻 X) 𝑨) → 𝑨 ⊧ p ≈ q  →  ∣ φ ∣ p ≡ ∣ φ ∣ q
 ⊧-H-invar φ Apq = {!!}
```
