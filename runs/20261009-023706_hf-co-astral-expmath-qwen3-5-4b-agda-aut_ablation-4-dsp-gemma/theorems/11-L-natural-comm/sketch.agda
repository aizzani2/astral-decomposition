{-# OPTIONS --without-K #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Category.Monoidal.Closed.IsClosed
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Product using (_,_)

open import Categories.Morphism.Reasoning C
open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₂)
import Categories.Category.Closed as Cls

open Closed Cl using (adjoint; [_,_]₀; [_,_]₁; [-,-]; unit; unitorˡ; -⊗_;
  module ⊗; [_,-]; [-,_])

private
  module C = Category C
  open Category C using (module HomReasoning; Obj; _⇒_; id; _∘_; _≈_;
    ∘-resp-≈ˡ; ∘-resp-≈ʳ)
  module ℱ = Functor

open HomReasoning
open adjoint using (Radjunct; Ladjunct; LRadjunct≈id; RLadjunct≈id; Radjunct-resp-≈) renaming (unit to η; counit to ε)

-- and here we use sub-modules in the hopes of making things go faster
open import Categories.Category.Monoidal.Closed.IsClosed.Identity Cl using (identity; diagonal)
open import Categories.Category.Monoidal.Closed.IsClosed.L Cl using (L; L-f-swap; L-g-swap)
open import Categories.Category.Monoidal.Closed.IsClosed.Dinatural Cl using (L-dinatural-comm)
open import Categories.Category.Monoidal.Closed.IsClosed.Diagonal Cl using (Lj≈j; jL≈i; iL≈i)
open import Categories.Category.Monoidal.Closed.IsClosed.Pentagon Cl using (pentagon′)

private
  id² : {S T : Obj} → [ S , T ]₀ ⇒ [ S , T ]₀
  id² = [ id , id ]₁

  -- dsp: lemmas
  -- dsp: end of lemmas
  L-natural-comm : {X Y′ Z′ Y Z : Obj} {f : Y′ ⇒ Y} {g : Z ⇒ Z′} →
                  L X Y′ Z′ ∘ [ f , g ]₁ ≈ [ [ id , f ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
  L-natural-comm {X = X} {Y′} {Z′} {Y} {Z} {f} {g} = {!!}
    where open C.HomReasoning
