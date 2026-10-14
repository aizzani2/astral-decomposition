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
  L-natural-comm : {X Y′ Z′ Y Z : Obj} {f : Y′ ⇒ Y} {g : Z ⇒ Z′} → L X Y′ Z′ ∘ [ f , g ]₁ ≈ [ [ id , f ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
  -- Step 7: put Phi = L X Y' Z' ∘ [f,g] and Psi = [[id,f],[id,g]] ∘ L X Y Z; by step 4, it suffices that the evaluations M_Phi and M_Psi agree.
  -- Step 8: both M_Phi and M_Psi live in [Y,Z] ⊗ A; by step 4 again, it suffices that ev ∘ (M_Phi ⊗ id_X) = ev ∘ (M_Psi ⊗ id_X).
  -- Steps 9-11: M_Phi = comp ∘ ([f,g] ⊗ id_A), so ev ∘ (M_Phi ⊗ id_X) = g ∘ ev ∘ (id ⊗ (f ∘ ev)) by steps 5 and 3 with p = f, q = g.
  -- Steps 12-14: M_Psi = [id,g] ∘ comp ∘ (id ⊗ [id,f]), and ev ∘ (M_Psi ⊗ id_X) = g ∘ ev ∘ (id ⊗ (ev ∘ ([id,f] ⊗ id_X))) by steps 3, 5, 6.
  -- Step 15: ev ∘ ([id_X,f] ⊗ id_X) = f ∘ ev by step 3 with p = id_X, q = f; so ev ∘ (M_Psi ⊗ id_X) = g ∘ ev ∘ (id ⊗ (f ∘ ev)).
  -- Step 16: the two sides agree, so M_Phi = M_Psi, hence Phi = Psi, that is, L X Y' Z' ∘ [f,g] ≈ [[id,f],[id,g]] ∘ L X Y Z.
  L-natural-comm = {!!}
