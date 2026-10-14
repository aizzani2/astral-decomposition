---
layout: default
file: "src/Demos/HSP.lagda.md"
title: "Demos.HSP module"
date: "2022-04-27"
author: "the agda-algebras development team"
---

### <a id="introduction">Introduction</a>

This module is the self-contained pedagogical companion to the TYPES 2021 paper [@DeMeo:2021].  The canonical statement and proof of Birkhoff's HSP theorem in agda-algebras now lives in [Setoid.Varieties.HSP][] (designated canonical under [issue #259](https://github.com/ualib/agda-algebras/issues/259), M2-4); the two presentations are co-extensive — this module's `Var⇒EqCl` and `Setoid.Varieties.HSP`'s `Birkhoff` prove the same theorem.  `Setoid.Varieties.HSP` is factored across the broader `Setoid.Varieties.*` development and is the appropriate import target for downstream uses, while this module collects the same proof into a single literate file and is preserved as a teaching artifact.

The Agda Universal Algebra Library ([agda-algebras][]) formalizes the foundations of universal 
algebra in intensional Martin-Löf type theory ([MLTT][]) using [Agda][] ()  [@Norell:2007; @agdaref].
The library includes a collection of definitions and verified theorems originated in classical 
(set-theory based) universal algebra and equational logic, but adapted to [MLTT][].

The first major milestone of the project is a complete formalization of *Birkhoff's variety
theorem* (also known as the *HSP theorem*) [@Birkhoff:1935]. To the best of our knowledge, this
is the first time Birkhoff's celebrated 1935 result has been formalized in [MLTT][].[^1]

Our first attempt to formalize Birkhoff's theorem suffered from two flaws.[^2] First, we 
assumed function extensionality in [MLTT][]; consequently, it was unclear whether the
formalization was fully constructive. Second, an inconsistency could be contrived by taking the
type `X`, representing an arbitrary collection of variable symbols, to be the two element type
(see §[7](#sec:discuss){reference-type="ref" reference="sec:discuss"} for details). To resolve
these issues, we developed a new formalization of the HSP theorem based on *setoids* and
rewrote much of the [agda-algebras][] library to support this approach. This enabled us to
avoid function extensionality altogether. Moreover, the type `X` of variable symbols was
treated with more care using the *context* and *environment* types that Andreas Abel uses
in [@Abel:2021] to formalize Birkhoff's completeness theorem. These design choices are
discussed further in §[2.2](#setoids){reference-type="ref"
reference="setoids"}--[2.3](#setoid-functions){reference-type="ref"
reference="setoid-functions"}.

What follows is a self-contained formal proof of the HSP theorem in [Agda][]. This is achieved
by extracting a subset of the library, including only the pieces needed for the proof, into a
single literate file.[^3] For spaces reasons, we elide some inessential parts, but strive to
preserve the essential content and character of the development. Specifically, routine or
overly technical components, as well as anything that does not seem to offer insight into the
central ideas of the proof are omitted. (The file [[src/Demos/HSP.lagda]{.sans-serif}](https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda) mentioned above includes the full proof.)

<!-- We include here every line of code of our new proof of Birkhoff's theorem in a single module, -->
<!-- presented as a literate document,[^4]. Apart from a few dozen imports from the , the module is self-contained. -->

In this paper, we highlight some of the more challenging aspects of formalizing universal algebra in type theory. To some extent, this is a sobering glimpse of the significant technical hurdles that must be overcome to do mathematics in dependent type theory. Nonetheless, we hope to demonstrate that [MLTT][] is a relatively natural language for formalizing universal algebra. Indeed, we believe that researchers with sufficient patience and resolve can reap the substantial rewards of deeper insight and greater confidence in their results by using type
theory and a proof assistant like [Agda][]. On the other hand, this paper is probably not the best place to learn about the latter, since we assume the reader is already familiar with [MLTT][] and [Agda][]. In summary, our main contribution is to show that a straightforward but very general representation of algebraic structures in dependent type theory is quite practical, as we demonstrate by formalizing a major seminal result of universal algebra.

### <a id="preliminaries">Preliminaries</a>

#### <a id="logical-foundations">Logical foundations</a>

To best emulate [MLTT][], we use

```agda
{-# OPTIONS --cubical-compatible --exact-split #-}
```

 disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29); 
directs [Agda][] to accept only definitions behaving like *judgmental* equalities;
**safe** ensures that nothing is postulated outright.
(See [@agdaref-axiomk; @agdaref-safeagda; @agdatools-patternmatching].)

Here are brief descriptions of these options, accompanied by links to
related documentation.

*  **without-K** disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29). See
   the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference Manual](https://agda.readthedocs.io/en/v2.6.1.3/language) [@agdaref-axiomk].

*  **exact-split** directs [Agda][] to accept only definitions behaving like *judgmental* equalities. See the [Pattern matching and equality](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) section of the [Agda Tools](https://agda.readthedocs.io/en/v2.6.1.3/tools/) documentation [@agdatools-patternmatching].

*  **safe** ensures that nothing is postulated outright---every non-axiom has to be an explicit assumption (e.g., an argument to a function or module). See the [cmdoption-safe](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) section of [@agdaref-safeagda].

We also make use of the following definitions from [Agda][]'s standard library (ver. 1.7).


```agda
-- Import universe levels and Signature type (described below) from the agda-algebras library.
open import Overture using ( 𝓞 ; 𝓥 ; Signature )
module Demos.HSP {𝑆 : Signature 𝓞 𝓥} where

-- Import 16 definitions from the Agda Standard Library.
open import Data.Unit.Polymorphic  using  ( ⊤ ; tt )
open import Function               using  ( id ; _∘_ ; flip )
open import Level                  using  ( Level ;  _⊔_ ; suc )
open import Relation.Binary        using  ( Rel ; Setoid ; IsEquivalence
                                          ; Reflexive ; Symmetric ; Transitive
                                          ; Sym ; Trans )
open import Relation.Unary         using  ( Pred ; _⊆_ ; _∈_ )

open import Relation.Binary.PropositionalEquality using ( _≡_ )

-- Import 23 definitions from the Agda Standard Library and rename 12 of them.
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _×_ ; _,_ ; Σ ; Σ-syntax )
                            renaming ( proj₁ to fst ; proj₂ to snd )
open import Function        using () renaming ( Func to _⟶_ )

open  _⟶_           using ( cong ) renaming ( to to _⟨$⟩_ )
open IsEquivalence  using ()
                    renaming ( refl to reflᵉ ; sym to symᵉ ; trans to transᵉ )
open Setoid         using ( Carrier ; isEquivalence ) renaming ( _≈_ to _≈ˢ_ )
                    renaming ( refl to reflˢ ; sym to symˢ ; trans to transˢ )

-- Assign handles to 3 modules of the Agda Standard Library.
import Function.Definitions                   as FD
import Relation.Binary.PropositionalEquality  as ≡
import Relation.Binary.Reasoning.Setoid       as SetoidReasoning

private variable
 α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ ρ χ ℓ : Level
 Γ Δ : Type χ
```


The above imports include some adjustments to "standard" [Agda][] syntax; in particular, we use `Type` in place of `Set`, the infix long arrow symbol, `_⟶_`, in place of `Func` (the type of "setoid functions," discussed in
§[2.3](#setoid-functions){reference-type="ref"
reference="setoid-functions"} below), and the symbol `_⟨$⟩_` in place of `f` (application of the map of a setoid function); we use `fst` and `snd`, and sometimes `∣_∣` and `∥_∥`, to denote the first and second projections out of the product type `_×_`.


```agda
module _ {A : Type α }{B : A → Type β} where
 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst
 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd
```



#### <a id="setoids">Setoids</a>

A *setoid* is a pair consisting of a type and an equivalence relation on that type. Setoids are useful for representing a set with an explicit, "local" notion of equivalence, instead of relying on an implicit, "global" one as is more common in set theory. In reality, informal mathematical practice relies on equivalence relations quite pervasively, taking great care to define only functions that preserve equivalences, while eliding the details. To be properly formal, such details must be made explicit. While there are many different workable approaches, the one that requires no additional meta-theory is based on setoids, which is why we adopt it here. While in some settings setoids are found by others to be burdensome, we have not found them to be so for universal algebra.

The [agda-algebras][] library was first developed without setoids, relying on propositional equality instead, along with some experimental, domain-specific types for equivalence classes, quotients, etc. This
required postulating function extensionality,[^4] which is known to be independent from [MLTT][] [@MHE; @MHE:2019]; this was unsatisfactory as we aimed to show that the theorems hold directly in [MLTT][] without extra axioms. The present work makes no appeal to functional extensionality or classical axioms like Choice or Excluded Middle.[^5]

##### <a id="setoid-functions">Setoid functions</a>

A *setoid function* is a function from one setoid to another that respects the underlying equivalences. If [𝑨]{.ab} and [𝑩]{.ab} are setoids, we use [𝑨]{.ab}_[⟶]{.aor}_[𝑩]{.ab} to denote the type of setoid functions from [𝑨]{.ab} to [𝑩]{.ab}.

An example of a setoid function is the identity function from a setoid to itself. We define it, along with a binary composition operation for setoid functions, `_⟨∘⟩_`, as follows.


```agda
𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
𝑖𝑑 {A} = record { to = id ; cong = id }

_⟨∘⟩_ :  {A : Setoid α ρᵃ} {B : Setoid β ρᵇ} {C : Setoid γ ρᶜ}
 →       B ⟶ C  →  A ⟶ B  →  A ⟶ C

f ⟨∘⟩ g = record  { to = (_⟨$⟩_ f) ∘ (_⟨$⟩_ g)
                  ; cong = (cong f) ∘ (cong g) }
```



#### <a id="inverses">Inverses</a>
<!-- {#inverses .unnumbered} -->

We define the *inverse* of a setoid function in terms of the image of the function's domain, as follows.


```agda
module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑩 using ( _≈_ ; sym ) renaming ( Carrier to B )

 data Image_∋_ (f : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
  eq : {b : B} → ∀ a → b ≈ f ⟨$⟩ a → Image f ∋ b
```


An inhabitant of the `Image f ∋ b` type is a point `a : Carrier 𝑨`, along with a proof `p : b ≈ f a`, that `f` maps `a` to `b`. Since a proof of `Image f ∋ b` must include a concrete witness `a : Carrier 𝑨`, we can actually *compute* a range-restricted right-inverse of `f`. Here is the definition of `Inv` which, for extra
certainty, is accompanied by a proof that it gives such a right-inverse.


```agda
 Inv : (f : 𝑨 ⟶ 𝑩){b : B} → Image f ∋ b → Carrier 𝑨
 Inv _ (eq a _) = a

 InvIsInverseʳ : {f : 𝑨 ⟶ 𝑩}{b : B}(q : Image f ∋ b) → f ⟨$⟩ (Inv f q) ≈ b
 InvIsInverseʳ (eq _ p) = sym p
```



#### <a id="injective-and-surjective-setoid-functions">Injective and surjective setoid functions</a>
<!-- {#injective-and-surjective-setoid-functions .unnumbered} -->

If `f : 𝑨 ⟶ 𝑩` then we call `f` *injective* provided `∀(a₀ a₁ : A)`, `f ⟨$⟩ a₀ ≈ᴮ f ⟨$⟩ a₁` implies `a₀ ≈ᴬ a₁`; we call `f` *surjective* provided `∀(b : B) ∃(a : A)` such that `f ⟨$⟩ a ≈ᴮ b`.

We represent injective functions on bare types by the type `Injective`, and use this to define the `IsInjective` type representing the property of being an injective setoid function. Similarly, the type `IsSurjective`
represents the property of being a surjective setoid function and `SurjInv` represents the *right-inverse* of a surjective function.

We reproduce the definitions and prove some of their properties inside the next submodule where we first set the stage by declaring two setoids `𝑨` and `𝑩` and naming their equality relations.


```agda
module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑨 using () renaming ( _≈_ to _≈ᴬ_ )
 open Setoid 𝑩 using () renaming ( _≈_ to _≈ᴮ_ )
 open FD

 IsInjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ ρᵃ ⊔ ρᵇ)
 IsInjective f = Injective _≈ᴬ_ _≈ᴮ_ (_⟨$⟩_ f)

 IsSurjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ β ⊔ ρᵇ)
 IsSurjective F = ∀ {y} → Image F ∋ y

 SurjInv : (f : 𝑨 ⟶ 𝑩) → IsSurjective f → Carrier 𝑩 → Carrier 𝑨
 SurjInv f fonto b = Inv f (fonto {b})
```


Proving that the composition of injective setoid functions is again injective is simply a matter of composing the two assumed witnesses to injectivity. Proving that surjectivity is preserved under composition is only slightly more involved.


```agda
module _  {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ}{𝑪 : Setoid γ ρᶜ}
          (f : 𝑨 ⟶ 𝑩)(g : 𝑩 ⟶ 𝑪) where

 ∘-IsInjective : IsInjective f → IsInjective g → IsInjective (g ⟨∘⟩ f)
 ∘-IsInjective finj ginj = finj ∘ ginj

 ∘-IsSurjective : IsSurjective f → IsSurjective g → IsSurjective (g ⟨∘⟩ f)
 ∘-IsSurjective fonto gonto {y} = Goal where
  mp : Image g ∋ y → Image g ⟨∘⟩ f ∋ y
  mp (eq c p) = η fonto where
   open Setoid 𝑪 using ( trans )
   η : Image f ∋ c → Image g ⟨∘⟩ f ∋ y
   η (eq a q) = eq a (trans p (cong g q))

  Goal : Image g ⟨∘⟩ f ∋ y
  Goal = mp gonto
```




#### <a id="factorization-of-setoid-functions">Factorization of setoid functions[^6]</a>
<!-- {#factorization-of-setoid-functions .unnumbered} -->

Every (setoid) function `f : A ⟶ B` factors as a surjective map `toIm : A ⟶ Im f` followed
by an injective map `fromIm : Im f ⟶ B`.


```agda
module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 Im : (f : 𝑨 ⟶ 𝑩) → Setoid _ _
 Carrier (Im f) = Carrier 𝑨
 _≈ˢ_ (Im f) b1 b2 = f ⟨$⟩ b1 ≈ f ⟨$⟩ b2 where open Setoid 𝑩

 isEquivalence (Im f) = record { refl = refl ; sym = sym; trans = trans }
  where open Setoid 𝑩

 toIm : (f : 𝑨 ⟶ 𝑩) → 𝑨 ⟶ Im f
 toIm f = record { to = id ; cong = cong f }

 fromIm : (f : 𝑨 ⟶ 𝑩) → Im f ⟶ 𝑩
 fromIm f = record { to = λ x → f ⟨$⟩ x ; cong = id }

 fromIm-inj : (f : 𝑨 ⟶ 𝑩) → IsInjective (fromIm f)
 fromIm-inj _ = id

 toIm-surj : (f : 𝑨 ⟶ 𝑩) → IsSurjective (toIm f)
 toIm-surj _ = eq _ (reflˢ 𝑩)
```



### <a id="basic-universal-algebra">Basic Universal Algebra</a>

We now develop a working vocabulary in [MLTT][] corresponding to classical, single-sorted, set-based universal algebra. We cover a number of important concepts, but limit ourselves to those required to prove Birkhoff's HSP theorem. In each case, we give a type-theoretic version of the informal definition, followed by its implementation in [Agda][].

This section is organized into the following subsections:
§[3.1](#signatures){reference-type="ref" reference="signatures"} defines
a general type of *signatures* of algebraic structures;
§[3.2](#algebras){reference-type="ref" reference="algebras"} does the
same for structures and their products;
§[3.3](#homomorphisms){reference-type="ref" reference="homomorphisms"}
defines *homomorphisms*, *monomorphisms*, and *epimorphisms*, presents
types that codify these concepts, and formally verifies some of their
basic properties; §[3.5](#subalgebras){reference-type="ref"
reference="subalgebras"}--[3.6](#terms){reference-type="ref"
reference="terms"} do the same for *subalgebras* and *terms*,
respectively.

#### <a id="signatures">Signatures</a>

An (algebraic) *signature* is a pair `𝑆 = (F, ρ)` where `F` is a collection of *operation symbols* and `ρ : F → N` is an *arity function* which maps each operation symbol to its arity. Here, `N` denotes the *arity type*. Heuristically, the arity of an operation symbol may be thought of as the number of arguments that takes as
"input."  We represent signatures as inhabitants of the following dependent pair type.

    Signature : (𝒪 𝒱 : Level) → Type (lsuc (𝒪 ⊔ 𝒱))
    Signature 𝒪 𝒱 = Σ[ F ∈ Type 𝒪 ] (F → Type 𝒱)

Recalling our syntax for the first and second projections, if `𝑆` is a signature, then `∣ 𝑆 ∣` denotes the set of operation symbols and `∥ 𝑆 ∥` denotes the arity function. Thus, if `f : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, then `∥ 𝑆 ∥ f` is the arity of `f`.

We need to augment our `Signature` type so that it supports algebras over setoid domains. To do so, following Abel [@Abel:2021], we define an operator that translates an ordinary signature into a *setoid signature*, that is, a signature over a setoid domain. This raises a minor technical issue: given operations `f` and `g`, with arguments `u : ∥ 𝑆 ∥ f → A` and `v : ∥ 𝑆 ∥ g → A`, respectively, and a proof of `f ≡ g` (*intensional* equality), we ought to be able to check whether `u` and `v` are *pointwise* equal. Technically, `u` and `v` appear to inhabit different types; of course, this is reconciled by the hypothesis `f ≡ g`, as we see in the next definition (borrowed from [@Abel:2021]).


```agda
EqArgs :  {𝑆 : Signature 𝓞 𝓥}{ξ : Setoid α ρᵃ}
 →        ∀ {f g} → f ≡ g → (∥ 𝑆 ∥ f → Carrier ξ) → (∥ 𝑆 ∥ g → Carrier ξ) → Type (𝓥 ⊔ ρᵃ)
EqArgs {ξ = ξ} ≡.refl u v = ∀ i → u i ≈ v i where open Setoid ξ using ( _≈_ )
```


This makes it possible to define an operator which translates a signature for algebras over bare types into a signature for algebras over setoids. We denote this operator by `⟨_⟩` and define it as follows.


```agda
⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρᵃ → Setoid _ _

Carrier  (⟨ 𝑆 ⟩ ξ)                = Σ[ f ∈ ∣ 𝑆 ∣ ] (∥ 𝑆 ∥ f → ξ .Carrier)
_≈ˢ_     (⟨ 𝑆 ⟩ ξ)(f , u)(g , v)  = Σ[ eqv ∈ f ≡ g ] EqArgs{ξ = ξ} eqv u v

reflᵉ   (isEquivalence (⟨ 𝑆 ⟩ ξ))                           = ≡.refl , λ i → reflˢ   ξ
symᵉ    (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)              = ≡.refl , λ i → symˢ    ξ (g i)
transᵉ  (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)(≡.refl , h)  = ≡.refl , λ i → transˢ  ξ (g i) (h i)
```



#### <a id="algebras">Algebras</a>

An *algebraic structure* `𝑨 = (A, Fᴬ)` *in the signature* `𝑆 = (F, ρ)`, or `𝑆`-*algebra*, consists of
*  a type `A`, called the *domain* of the algebra;
*  a collection `Fᴬ := {fᴬ ∣ f ∈ F, fᴬ : (ρ f → A) → A}` of *operations* on `A`;
*  a (potentially empty) collection of *identities* satisfied by elements and operations of `𝑨`.
Our [Agda][] implementation represents algebras as inhabitants of a record type with two fields---a `Domain` setoid denoting the domain of the algebra, and an `Interp` function denoting the interpretation in the algebra of each operation symbol in `𝑆`. We postpone introducing identities until §[4](#equational-logic){reference-type="ref" reference="equational-logic"}.


```agda
record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ suc (α ⊔ ρ)) where
 field  Domain  : Setoid α ρ
        Interp  : ⟨ 𝑆 ⟩ Domain ⟶ Domain
```


Thus, for each operation symbol in `𝑆` we have a setoid function `f` whose domain is a power of `Domain` and whose codomain is `Domain`. Further, we define some syntactic sugar to make our formalizations easier to read and reason about. Specifically, if `𝑨` is an algebra, then
*  `𝔻[ 𝑨 ]` denotes the `Domain` setoid of `𝑨`,
*  `𝕌[ 𝑨 ]` is the underlying carrier of (the `Domain` setoid of) `𝑨`, and
*  `f ̂ 𝑨` denotes the interpretation of the operation symbol `f` in the algebra `𝑨`.


```agda
open Algebra
𝔻[_] : Algebra α ρᵃ →  Setoid α ρᵃ
𝔻[ 𝑨 ] = Domain 𝑨

𝕌[_] : Algebra α ρᵃ →  Type α
𝕌[ 𝑨 ] = Carrier (Domain 𝑨)

_̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra α ρᵃ) → (∥ 𝑆 ∥ f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]
f ̂ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)
```


#### <a id="universe-levels-of-algebra-types">Universe levels of algebra types</a>
<!-- {#universe-levels-of-algebra-types .unnumbered} -->

Types belong to *universes*, which are structured in [Agda][] as follows: 
`Type ℓ : Type (suc ℓ)`, `Type (suc ℓ) : Type (suc (suc ℓ))`.[^7] 
While this means that `Type ℓ` has type `Type (suc ℓ)`, it does *not* imply that `Type ℓ` 
has type `Type (suc (suc ℓ))`. In other words, [Agda][]'s universes are *non-cumulative*. 
This can be advantageous as it becomes possible to treat size issues more generally and precisely. 
However, dealing with explicit universe levels can be daunting, and the standard literature
(in which uniform smallness is typically assumed) offers little guidance. While in some settings, 
such as category theory, formalizing in [Agda][] works smoothly with respect to universe levels 
(see [@agda-categories]), in universal algebra the terrain is bumpier. Thus, it seems worthwhile to 
explain how we make use of universe lifting and lowering functions, available in the 
[Agda Standard Library][], to develop domain-specific tools for dealing with [Agda][]'s non-cumulative 
universe hierarchy.

<!-- Let us be more concrete about what is at issue by considering a typical example. frequently encounters problems during the type-checking process and responds by printing a message like the following. Here informs us that it encountered universe level on line 498 of the HSP module, where it was expecting level     ( ). In this case, we tried to use an algebra inhabiting the type whereas expected an inhabitant of the type ( ( )) . The operation of the standard library embeds a type into a higher universe. Specializing to our situation, we define a function  with the following interface. -2mm . -->

The `Lift` operation of the standard library embeds a type into a higher universe. Specializing `Lift` to our situation, we define a function `Lift-Alg`.


```agda
module _ (𝑨 : Algebra α ρᵃ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans ) ; open Level
 Lift-Algˡ : (ℓ : Level) → Algebra (α ⊔ ℓ) ρᵃ
 Domain (Lift-Algˡ ℓ) =
  record  { Carrier        = Lift ℓ 𝕌[ 𝑨 ]
          ; _≈_            = λ x y → lower x ≈ lower y
          ; isEquivalence  = record { refl = refl ; sym = sym ; trans = trans }
          }
 Interp (Lift-Algˡ ℓ) ⟨$⟩ (f , la) = lift ((f ̂ 𝑨) (lower ∘ la))
 cong (Interp (Lift-Algˡ ℓ)) (≡.refl , lab) = cong (Interp 𝑨) ((≡.refl , lab))

 Lift-Algʳ : (ℓ : Level) → Algebra α (ρᵃ ⊔ ℓ)
 Domain (Lift-Algʳ ℓ) =
  record  { Carrier        = 𝕌[ 𝑨 ]
          ; _≈_            = λ x y → Lift ℓ (x ≈ y)
          ; isEquivalence  = record  { refl  = lift refl
                                     ; sym   = lift ∘ sym ∘ lower
                                     ; trans = λ x y → lift (trans (lower x)(lower y))
                                     }
          }
 Interp (Lift-Algʳ ℓ ) ⟨$⟩ (f , la) = (f ̂ 𝑨) la
 cong (Interp (Lift-Algʳ ℓ))(≡.refl , lab) =
  lift ( cong (Interp 𝑨) ( ≡.refl , λ i → lower (lab i) ) )

Lift-Alg : Algebra α ρᵃ → (ℓ₀ ℓ₁ : Level) → Algebra (α ⊔ ℓ₀) (ρᵃ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ ℓ₁ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀) ℓ₁
```


Recall that our `Algebra` type has two universe level parameters corresponding to
those of the domain setoid. Concretely, an algebra of type `Algebra α ρᵃ` has a
`Domain` of type `Setoid α ρᵃ`. This packages a  "carrier set" (`Carrier`),
inhabiting `Type α`, with an equality on `Carrier` of type `Rel Carrier ρᵃ`.
`Lift-Alg` takes an algebra parametrized by levels `α` and `ρᵃ` and constructs a
new algebra whose carrier  inhabits `Type (α ⊔ ℓ₀)` and whose equivalence inhabits
`Rel Carrier (ρᵃ ⊔ ℓ₁)`. To be useful, this lifting operation should result in an
algebra with the same semantic properties as the one we started with. We will see
in §[3.4](#sec:lift-alg){reference-type="ref" reference="sec:lift-alg"} that this
is indeed the case.


#### <a id="product-algebras">Product Algebras</a>
 <!-- {#product-algebras .unnumbered} -->

We define the *product* of a family of algebras as follows. Let `ι` be a universe
and `I : Type ι` a type (the "indexing type"). Then `𝒜 : I → Algebra α ρᵃ`
represents an *indexed family of algebras*. Denote by `⨅ 𝒜` the *product of
algebras* in `𝒜` (or *product algebra*), by which we mean the algebra whose domain
is the Cartesian product `∏[i ∈ I] 𝔻[ 𝒜 i ]` of the domains of the algebras in
`𝒜`, and whose operations are those arising from the point-wise interpretation of
the operation symbols in the obvious way: if `f` is a `J`-ary operation symbol and
if `a : Π[ i ∈ I ] J → 𝔻[ 𝒜 i ]` is, for each `i : I`, a `J`-tuple of elements of
the domain `𝔻[ 𝒜 i ]`, then we define the interpretation of `f` in `⨅ 𝒜` by

`(f ̂ ⨅ 𝒜) a := λ (i : I) → (f ̂ 𝒜 i)(a i)`.

Here is the formal definition of the product algebra type in [Agda][].


```agda
module _ {ι : Level}{I : Type ι } where

 ⨅ : (𝒜 : I → Algebra α ρᵃ) → Algebra (α ⊔ ι) (ρᵃ ⊔ ι)
 Domain (⨅ 𝒜) =
  record  { Carrier = ∀ i → 𝕌[ 𝒜 i ]
          ; _≈_ = λ a b → ∀ i → (_≈ˢ_ 𝔻[ 𝒜 i ]) (a i)(b i)
          ; isEquivalence =
             record  { refl = λ i → reflᵉ (isEquivalence 𝔻[ 𝒜 i ])
                     ; sym = λ x i → symᵉ (isEquivalence 𝔻[ 𝒜 i ])(x i)
                     ; trans = λ x y i → transᵉ (isEquivalence 𝔻[ 𝒜 i ])(x i)(y i)
                     }
          }

 Interp (⨅ 𝒜) ⟨$⟩ (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
 cong (Interp (⨅ 𝒜)) (≡.refl , f=g ) = λ i → cong  ( Interp (𝒜 i) )
                                                   ( ≡.refl , flip f=g i )
```


Evidently, the carrier of the product algebra type is indeed the (dependent)
product of the carriers in the indexed family. The rest of the definitions are the
point-wise versions of the underlying ones.

#### <a id="structure-preserving-maps-and-isomorphism">Structure preserving maps and isomorphism</a>

Throughout the rest of the paper, unless stated otherwise, `𝑨` and `𝑩` will denote
`𝑆`-algebras inhabiting the types `Algebra α ρᵃ` and `Algebra β ρᵇ`, respectively.

A *homomorphism* (or "hom") from `𝑨` to `𝑩` is a setoid function
`h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]` that is *compatible* with all basic operations; that is, for
every operation symbol `f : ∣ 𝑆 ∣` and all tuples `a : ∥ 𝑆 ∥ f → 𝕌[ 𝑨 ]`, we have
`h ⟨$⟩ (f ̂ 𝑨) a ≈ (f ̂ 𝑩) λ x → h ⟨$⟩ (a x)`.

It is convenient to first formalize "compatible" (`compatible-map-op`),
representing the assertion that a given setoid function `h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]`
commutes with a given operation symbol `f`, and then generalize over operation
symbols to yield the type (`compatible-map`) of compatible maps from (the domain
of) `𝑨` to (the domain of) `𝑩`.


```agda
module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where

 compatible-map-op : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → ∣ 𝑆 ∣ → Type _
 compatible-map-op h f = ∀ {a} → h ⟨$⟩ (f ̂ 𝑨) a ≈ (f ̂ 𝑩) λ x → h ⟨$⟩ (a x)
  where open Setoid 𝔻[ 𝑩 ] using ( _≈_ )

 compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type _
 compatible-map h = ∀ {f} → compatible-map-op h f
```


Using these we define the property (`IsHom`) of being a homomorphism, and
finally the type (`hom`) of homomorphisms from `𝑨` to `𝑩`.


```agda
 record IsHom (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ) where
  constructor  mkhom
  field        compatible : compatible-map h

 hom : Type _
 hom = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsHom
```


Thus, an inhabitant of `hom 𝑨 𝑩` is a pair `(h , p)` consisting of a setoid
function `h`, from the domain of `𝑨` to that of `𝑩`, along with a proof `p` that
`h` is a homomorphism.

A *monomorphism* (resp. *epimorphism*) is an injective (resp. surjective)
homomorphism. The [agda-algebras][] library defines predicates and for these, as
well as and for the corresponding types.


```agda
 record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
  field  isHom : IsHom h
         isInjective : IsInjective h
  HomReduct : hom
  HomReduct = h , isHom

 mon : Type _
 mon = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsMon
```


As with `hom`, the type `mon` is a dependent product type; each inhabitant is a
pair consisting of a setoid function, say, `h`, along with a proof that `h` is a
monomorphism.


```agda
 record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵇ) where
  field  isHom : IsHom h
         isSurjective : IsSurjective h
  HomReduct : hom
  HomReduct = h , isHom

 epi : Type _
 epi = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsEpi
```


Here are two utilities that are useful for translating between types.


```agda
open IsHom ; open IsMon ; open IsEpi
module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
 mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
 mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

 epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective ∣ h ∣
 epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE
```


##### <a id="composition-of-homomorphisms">Composition of homomorphisms</a>
 <!-- {#composition-of-homomorphisms .unnumbered} -->

The composition of homomorphisms is again a homomorphism, and similarly
for epimorphisms and monomorphisms. The proofs of these facts are
straightforward.


```agda
module _  {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ}
          {g : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]}{h : 𝔻[ 𝑩 ] ⟶ 𝔻[ 𝑪 ]} where
  open Setoid 𝔻[ 𝑪 ] using ( trans )
  -- dsp: lemmas
  -- dsp: end of lemmas
  ∘-is-hom : IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h → IsHom 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-hom = (λ { x x₁ → (mkhom (λ {f} {a} → transᵉ (isEquivalence (𝑪 .Domain)) (h .cong (x .compatible)) (x₁ .compatible))) })
```
