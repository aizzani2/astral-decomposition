{-# OPTIONS --without-K #-}
module Categories.Category.Unbundled.Properties where

-- The Obj-unbundled Category is equivalent (as a type) to the
-- usual kind. Quite straightforward and because of η, the proofs are just refl.

open import Data.Product using (Σ; _,_)
open import Level
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Category.Core using (Category)
open import Categories.Category.Unbundled renaming (Category to Unb-Cat)

private
  variable
    o ℓ e : Level

unpack : Category o ℓ e → Σ (Set o) (λ Obj → Unb-Cat Obj ℓ e)
unpack C = C.Obj , record { C }
  where module C = Category C

unpack′ : (C : Category o ℓ e) → Unb-Cat (Category.Obj C) ℓ e
unpack′ C = record { C }
  where module C = Category C

pack : Σ (Set o) (λ Obj → Unb-Cat Obj ℓ e) → Category o ℓ e
pack (o , uc)  = record { Obj = o; UC }
  where module UC = Unb-Cat uc

pack′ :  {Obj : Set o} → Unb-Cat Obj ℓ e → Category o ℓ e
pack′ {Obj = o} uc  = record { Obj = o; UC }
  where module UC = Unb-Cat uc

-- dsp: lemmas
equiv-gap0 : {o : Level} → {ℓ : Level} → {e : Level} → Category o ℓ e ↔ Σ (Set o) (λ Obj → Unb-Cat Obj ℓ e)
equiv-gap0 = mk↔ₛ′ (λ C → unpack C) (λ uc → pack uc) (λ uc → refl) (λ C → refl)

-- dsp: end of lemmas
equiv : (Category o ℓ e) ↔ (Σ (Set o) (λ Obj → Unb-Cat Obj ℓ e))
equiv = equiv-gap0
