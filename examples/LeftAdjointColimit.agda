{-# OPTIONS --without-K #-}

module LeftAdjointColimit where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong)

record Category (o h : Level) : Set (lsuc (o ⊔ h)) where
  field
    Ob    : Set o
    Hom   : Ob → Ob → Set h
    id    : ∀ {x} → Hom x x
    _∘_   : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    idˡ   : ∀ {x y} (f : Hom x y) → (id ∘ f) ≡ f
    idʳ   : ∀ {x y} (f : Hom x y) → (f ∘ id) ≡ f
    assoc : ∀ {w x y z} (f : Hom y z) (g : Hom x y) (k : Hom w x)
          → ((f ∘ g) ∘ k) ≡ (f ∘ (g ∘ k))

record Functor {o h o' h'} (C : Category o h) (D : Category o' h')
  : Set (o ⊔ h ⊔ o' ⊔ h') where
  private module C = Category C
  private module D = Category D
  field
    F₀   : C.Ob → D.Ob
    F₁   : ∀ {x y} → C.Hom x y → D.Hom (F₀ x) (F₀ y)
    F-id : ∀ {x} → F₁ (C.id {x}) ≡ D.id
    F-∘  : ∀ {x y z} (f : C.Hom y z) (g : C.Hom x y)
         → F₁ (f C.∘ g) ≡ (F₁ f D.∘ F₁ g)

record Cocone {oj hj o h} {J : Category oj hj} {C : Category o h}
              (Dia : Functor J C) (N : Category.Ob C)
  : Set (oj ⊔ hj ⊔ h) where
  private module J  = Category J
  private module C  = Category C
  private module DD = Functor Dia
  field
    ι    : ∀ j → C.Hom (DD.F₀ j) N
    comm : ∀ {i j} (u : J.Hom i j) → (ι j C.∘ DD.F₁ u) ≡ ι i

-- A cocone is colimiting iff it is initial among cocones
record IsColimit {oj hj o h} {J : Category oj hj} {C : Category o h}
                 {Dia : Functor J C} {N : Category.Ob C} (cone : Cocone Dia N)
  : Set (oj ⊔ hj ⊔ o ⊔ h) where
  private module C = Category C
  private module J = Category J
  open Cocone cone
  field
    chosen : ∀ {M} (other : Cocone Dia M) → C.Hom N M
    factor : ∀ {M} (other : Cocone Dia M) (j : J.Ob)
           → (chosen other C.∘ ι j) ≡ Cocone.ι other j
    unique : ∀ {M} (other : Cocone Dia M) (m : C.Hom N M)
           → (∀ j → (m C.∘ ι j) ≡ Cocone.ι other j)
           → m ≡ chosen other

record _≃_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

-- F ⊣ G via a natural iso of hom-sets, natural in each variable.
record Adjunction {o h o' h'} {C : Category o h} {D : Category o' h'}
                  (F : Functor C D) (G : Functor D C)
  : Set (o ⊔ h ⊔ o' ⊔ h') where
  private module C = Category C
  private module D = Category D
  open Functor F using () renaming (F₀ to F₀; F₁ to F₁)
  open Functor G using () renaming (F₀ to G₀; F₁ to G₁)
  field
    Φ      : ∀ {a d} → D.Hom (F₀ a) d ≃ C.Hom a (G₀ d)
    Φ-natˡ : ∀ {a' a d} (h : C.Hom a' a) (f : D.Hom (F₀ a) d)
           → _≃_.to Φ (f D.∘ F₁ h) ≡ (_≃_.to Φ f C.∘ h)
    Φ-natʳ : ∀ {a d d'} (k : D.Hom d d') (f : D.Hom (F₀ a) d)
           → _≃_.to Φ (k D.∘ f) ≡ (G₁ k C.∘ _≃_.to Φ f)

-- Composite Functor
_∘F_ : ∀ {oj hj o h o' h'} {J : Category oj hj} {C : Category o h} {D : Category o' h'}
     → Functor C D → Functor J C → Functor J D
_∘F_ F Dia = record
  { F₀  = λ j → FF.F₀ (DD.F₀ j)
  ; F₁  = λ u → FF.F₁ (DD.F₁ u)
  ; F-id = trans (cong FF.F₁ DD.F-id) FF.F-id
  ; F-∘  = λ f g → trans (cong FF.F₁ (DD.F-∘ f g)) (FF.F-∘ (DD.F₁ f) (DD.F₁ g))
  }
  where module FF = Functor F
        module DD = Functor Dia

pushCocone : ∀ {oj hj o h o' h'} {J : Category oj hj} {C : Category o h} {D : Category o' h'}
             (F : Functor C D) {Dia : Functor J C} {N : Category.Ob C}
           → Cocone Dia N → Cocone (F ∘F Dia) (Functor.F₀ F N)
pushCocone F {Dia} cone = record
  { ι    = λ j → FF.F₁ (Cocone.ι cone j)
  ; comm = λ {i} {j} u →
      trans (sym (FF.F-∘ (Cocone.ι cone j) (Functor.F₁ Dia u)))
            (cong FF.F₁ (Cocone.comm cone u))
  }
  where module FF = Functor F

left-adjoint-preserves-colimit :
  ∀ {oj hj o h o' h'} {J : Category oj hj} {C : Category o h} {D : Category o' h'}
    {F : Functor C D} {G : Functor D C}
  → Adjunction F G
  → {Dia : Functor J C} {N : Category.Ob C} (cone : Cocone Dia N)
  → IsColimit cone
  → IsColimit (pushCocone F cone)
left-adjoint-preserves-colimit adj cone colim = ?