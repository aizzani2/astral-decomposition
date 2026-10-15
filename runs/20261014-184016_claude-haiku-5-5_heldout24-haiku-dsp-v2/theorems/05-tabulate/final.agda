------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Any
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.List.Relation.Unary.Any.Properties where

open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (T-∨; T-≡)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base as List hiding (find; and; or; all; any)
open import Data.List.Effectful as List using (monad)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties.Core
  using (Any↔; find∘map; map∘find; lose∘find)
open import Data.List.Relation.Binary.Pointwise
  using (Pointwise; []; _∷_)
open import Data.Nat.Base using (zero; suc; _<_; z<s; s<s; s≤s)
open import Data.Nat.Properties using (_≡?_; ≤∧≢⇒<; ≤-refl; m<n⇒m<1+n)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.Any as MAny using (just)
open import Data.Product.Base as Product
  using (_×_; _,_; ∃; ∃₂; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Propositional
  using (_×-cong_)
import Data.Product.Function.Dependent.Propositional as Σ
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Function.Propositional using (_⊎-cong_)
open import Effect.Monad using (RawMonad)
open import Function.Base using (_$_; _∘_; flip; const; id; _∘′_)
open import Function.Bundles
import Function.Properties.Inverse as Inverse
open import Function.Related.Propositional as Related using (Kind; Related)
open import Level using (Level)
open import Relation.Binary.Core using (Rel; REL)
open import Relation.Binary.Definitions as B
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; resp)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Unary as U
  using (Pred; _⟨×⟩_; _⟨→⟩_) renaming (_⊆_ to _⋐_)
open import Relation.Nullary.Decidable.Core
  using (¬?; _because_; does; yes; no; decidable-stable)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (invert)

private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

private
  variable
    a b c p q r ℓ : Level
    A B C : Set a
    P Q R : Pred A p
    x y : A
    xs ys : List A

------------------------------------------------------------------------
-- Equality properties

lift-resp : ∀ {_≈_ : Rel A ℓ} → P Respects _≈_ →
            (Any P) Respects (Pointwise _≈_)
lift-resp resp (x≈y ∷ xs≈ys) (here px)   = here (resp x≈y px)
lift-resp resp (x≈y ∷ xs≈ys) (there pxs) = there (lift-resp resp xs≈ys pxs)

here-injective : ∀ {p q : P x} → here {P = P} {xs = xs} p ≡ here q → p ≡ q
here-injective refl = refl

there-injective : ∀ {p q : Any P xs} → there {x = x} p ≡ there q → p ≡ q
there-injective refl = refl

------------------------------------------------------------------------
-- Misc

¬Any[] : ¬ Any P []
¬Any[] ()

------------------------------------------------------------------------
-- Any is a congruence

Any-cong : ∀ {k : Kind} → (∀ x → Related k (P x) (Q x)) →
           (∀ {z} → Related k (z ∈ xs) (z ∈ ys)) →
           Related k (Any P xs) (Any Q ys)
Any-cong {P = P} {Q = Q} {xs = xs} {ys} P↔Q xs≈ys =
  Any P xs                ↔⟨ Related.SK-sym Any↔ ⟩
  (∃ λ x → x ∈ xs × P x)  ∼⟨ Σ.cong Inverse.↔-refl (xs≈ys ×-cong P↔Q _) ⟩
  (∃ λ x → x ∈ ys × Q x)  ↔⟨ Any↔ ⟩
  Any Q ys                ∎
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- Any.map

map-cong : (f g : P ⋐ Q) → (∀ {x} (p : P x) → f p ≡ g p) →
          (p : Any P xs) → Any.map f p ≡ Any.map g p
map-cong f g hyp (here  p) = cong here (hyp p)
map-cong f g hyp (there p) = cong there $ map-cong f g hyp p

map-id : ∀ (f : P ⋐ P) → (∀ {x} (p : P x) → f p ≡ p) →
         (p : Any P xs) → Any.map f p ≡ p
map-id f hyp (here  p) = cong here (hyp p)
map-id f hyp (there p) = cong there $ map-id f hyp p

map-∘ : ∀ (f : Q ⋐ R) (g : P ⋐ Q) (p : Any P xs) →
        Any.map (f ∘ g) p ≡ Any.map f (Any.map g p)
map-∘ f g (here  p) = refl
map-∘ f g (there p) = cong there $ map-∘ f g p

------------------------------------------------------------------------
-- Any.lookup

lookup-result : ∀ (p : Any P xs) → P (Any.lookup p)
lookup-result (here px) = px
lookup-result (there p) = lookup-result p

lookup-index : ∀ (p : Any P xs) → P (lookup xs (Any.index p))
lookup-index (here px)   = px
lookup-index (there pxs) = lookup-index pxs

------------------------------------------------------------------------
-- Swapping

-- Nested occurrences of Any can sometimes be swapped. See also ×↔.

module _ {R : REL A B ℓ} where

  swap : Any (λ x → Any (R x) ys) xs → Any (λ y → Any (flip R y) xs) ys
  swap (here  pys)  = Any.map here pys
  swap (there pxys) = Any.map there (swap pxys)

  swap-there : (any : Any (λ x → Any (R x) ys) xs) →
               swap (Any.map (there {x = x}) any) ≡ there (swap any)
  swap-there (here  pys)  = refl
  swap-there (there pxys) = cong (Any.map there) (swap-there pxys)

module _ {R : REL A B ℓ} where

  swap-invol : (any : Any (λ x → Any (R x) ys) xs) →
               swap (swap any) ≡ any
  swap-invol (here (here px))   = refl
  swap-invol (here (there pys)) =
    cong (Any.map there) (swap-invol (here pys))
  swap-invol (there pxys)       =
    trans (swap-there (swap pxys)) (cong there (swap-invol pxys))

module _ {R : REL A B ℓ} where

  swap↔ : Any (λ x → Any (R x) ys) xs ↔ Any (λ y → Any (flip R y) xs) ys
  swap↔ = mk↔ₛ′ swap swap swap-invol swap-invol

------------------------------------------------------------------------
-- Lemmas relating Any to ⊥

⊥↔Any⊥ : ⊥ ↔ Any (const ⊥) xs
⊥↔Any⊥ = mk↔ₛ′ (λ()) (λ p → from p) (λ p → from p) (λ())
  where
  from : Any (const ⊥) xs → B
  from (there p) = from p

⊥↔Any[] : ⊥ ↔ Any P []
⊥↔Any[] = mk↔ₛ′ (λ()) (λ()) (λ()) (λ())

------------------------------------------------------------------------
-- Lemmas relating Any to ⊤

-- These introduction and elimination rules are not inverses, though.

any⁺ : ∀ (p : A → Bool) → Any (T ∘ p) xs → T (any p xs)
any⁺ p (here  px)          = Equivalence.from T-∨ (inj₁ px)
any⁺ p (there {x = x} pxs) with p x
... | true  = _
... | false = any⁺ p pxs

any⁻ : ∀ (p : A → Bool) xs → T (any p xs) → Any (T ∘ p) xs
any⁻ p (x ∷ xs) px∷xs with p x in eq
... | true  = here (Equivalence.from T-≡ eq)
... | false = there (any⁻ p xs px∷xs)

any⇔ : ∀ {p : A → Bool} → Any (T ∘ p) xs ⇔ T (any p xs)
any⇔ = mk⇔ (any⁺ _) (any⁻ _ _)

------------------------------------------------------------------------
-- Sums commute with Any

Any-⊎⁺ : Any P xs ⊎ Any Q xs → Any (λ x → P x ⊎ Q x) xs
Any-⊎⁺ = [ Any.map inj₁ , Any.map inj₂ ]′

Any-⊎⁻ : Any (λ x → P x ⊎ Q x) xs → Any P xs ⊎ Any Q xs
Any-⊎⁻ (here (inj₁ p)) = inj₁ (here p)
Any-⊎⁻ (here (inj₂ q)) = inj₂ (here q)
Any-⊎⁻ (there p)       = Sum.map there there (Any-⊎⁻ p)

⊎↔ : (Any P xs ⊎ Any Q xs) ↔ Any (λ x → P x ⊎ Q x) xs
⊎↔ {P = P} {Q = Q} = mk↔ₛ′ Any-⊎⁺ Any-⊎⁻ to∘from from∘to
  where
  from∘to : (p : Any P xs ⊎ Any Q xs) → Any-⊎⁻ (Any-⊎⁺ p) ≡ p
  from∘to (inj₁ (here  p)) = refl
  from∘to (inj₁ (there p)) rewrite from∘to (inj₁ p) = refl
  from∘to (inj₂ (here  q)) = refl
  from∘to (inj₂ (there q)) rewrite from∘to (inj₂ q) = refl

  to∘from : (p : Any (λ x → P x ⊎ Q x) xs) → Any-⊎⁺ (Any-⊎⁻ p) ≡ p
  to∘from (here (inj₁ p)) = refl
  to∘from (here (inj₂ q)) = refl
  to∘from (there p) with Any-⊎⁻ p | to∘from p
  ... | inj₁ p | refl = refl
  ... | inj₂ q | refl = refl

------------------------------------------------------------------------
-- Products "commute" with Any.

Any-×⁺ : Any P xs × Any Q ys → Any (λ x → Any (λ y → P x × Q y) ys) xs
Any-×⁺ (p , q) = Any.map (λ p → Any.map (λ q → (p , q)) q) p

Any-×⁻ : Any (λ x → Any (λ y → P x × Q y) ys) xs →
         Any P xs × Any Q ys
Any-×⁻ pq = let x , x∈xs , pq′ = find pq in
            let y , y∈ys , p , q = find pq′ in
            lose x∈xs p , lose y∈ys q

×↔ : ∀ {xs ys} →
     (Any P xs × Any Q ys) ↔ Any (λ x → Any (λ y → P x × Q y) ys) xs
×↔ {P = P} {Q = Q} {xs} {ys} = mk↔ₛ′ Any-×⁺ Any-×⁻ to∘from from∘to
  where
  open ≡-Reasoning

  from∘to : ∀ pq → Any-×⁻ (Any-×⁺ pq) ≡ pq
  from∘to (p , q) = let x , x∈xs , px = find p in

    Any-×⁻ (Any-×⁺ (p , q))

     ≡⟨⟩

    (let (x , x∈xs , pq)    = find (Any-×⁺ (p , q))
         (y , y∈ys , p , q) = find pq
     in  lose x∈xs p , lose y∈ys q)

     ≡⟨ cong (λ • → let (x , x∈xs , pq)    = •
                        (y , y∈ys , p , q) = find pq
                    in  lose x∈xs p , lose y∈ys q)
             (find∘map p (λ p → Any.map (p ,_) q)) ⟩

    (let (x , x∈xs , p)     = find p
         (y , y∈ys , p , q) = find (Any.map (p ,_) q)
     in  lose x∈xs p , lose y∈ys q)

     ≡⟨ cong (λ • → let (x , x∈xs , _)     = find p
                        (y , y∈ys , p , q) = •
                    in  lose x∈xs p , lose y∈ys q)
             (find∘map q (px ,_)) ⟩

    (let (x , x∈xs , p) = find p
         (y , y∈ys , q) = find q
     in  lose x∈xs p , lose y∈ys q)

     ≡⟨ cong₂ _,_ (lose∘find p) (lose∘find q) ⟩

    (p , q) ∎

  to∘from : ∀ pq → Any-×⁺ (Any-×⁻ pq) ≡ pq
  to∘from pq =
    let x , x∈xs , pq′ = find pq
        y , y∈ys , px , qy = find pq′

        h : P ⋐ λ x → Any (λ y → (P x) × (Q y)) ys
        h p = Any.map (p ,_) (lose y∈ys qy)

        helper : h px ≡ pq′
        helper = begin
          Any.map (px ,_) (lose y∈ys qy)
            ≡⟨ map-∘ (px ,_) (λ z → resp Q z qy) y∈ys ⟨
          Any.map (λ z → px , resp Q z qy) y∈ys
            ≡⟨ map∘find pq′ refl ⟩
          pq′
            ∎

    in  begin
      Any-×⁺ (Any-×⁻ pq)
        ≡⟨⟩
      Any.map h (lose x∈xs px)
        ≡⟨ map-∘ h (λ z → resp P z px) x∈xs ⟨
      Any.map (λ z → Any.map (resp P z px ,_) (lose y∈ys qy)) x∈xs
        ≡⟨ map∘find pq helper ⟩
      pq
        ∎

------------------------------------------------------------------------
-- Half-applied product commutes with Any.

module _ {_~_ : REL A B r} where

  Any-Σ⁺ʳ : (∃ λ x → Any (_~ x) xs) → Any (∃ ∘ _~_) xs
  Any-Σ⁺ʳ (b , here px) = here (b , px)
  Any-Σ⁺ʳ (b , there pxs) = there (Any-Σ⁺ʳ (b , pxs))

  Any-Σ⁻ʳ : Any (∃ ∘ _~_) xs → ∃ λ x → Any (_~ x) xs
  Any-Σ⁻ʳ (here (b , x)) = b , here x
  Any-Σ⁻ʳ (there xs) = Product.map₂ there $ Any-Σ⁻ʳ xs

------------------------------------------------------------------------
-- Invertible introduction (⁺) and elimination (⁻) rules for various
-- list functions
------------------------------------------------------------------------

------------------------------------------------------------------------
-- singleton

singleton⁺ : P x → Any P [ x ]
singleton⁺ Px = here Px

singleton⁻ : Any P [ x ] → P x
singleton⁻ (here Px) = Px

------------------------------------------------------------------------
-- map

module _ {f : A → B} where

  map⁺ : Any (P ∘ f) xs → Any P (List.map f xs)
  map⁺ (here p)  = here p
  map⁺ (there p) = there $ map⁺ p

  map⁻ : Any P (List.map f xs) → Any (P ∘ f) xs
  map⁻ {xs = x ∷ xs} (here p)  = here p
  map⁻ {xs = x ∷ xs} (there p) = there $ map⁻ p

  map⁺∘map⁻ : (p : Any P (List.map f xs)) → map⁺ (map⁻ p) ≡ p
  map⁺∘map⁻ {xs = x ∷ xs} (here  p) = refl
  map⁺∘map⁻ {xs = x ∷ xs} (there p) = cong there (map⁺∘map⁻ p)

  map⁻∘map⁺ : ∀ (P : Pred B p) →
              (p : Any (P ∘ f) xs) → map⁻ {P = P} (map⁺ p) ≡ p
  map⁻∘map⁺ P (here  p) = refl
  map⁻∘map⁺ P (there p) = cong there (map⁻∘map⁺ P p)

  map↔ : Any (P ∘ f) xs ↔ Any P (List.map f xs)
  map↔ = mk↔ₛ′ map⁺ map⁻ map⁺∘map⁻ (map⁻∘map⁺ _)

  gmap : P ⋐ Q ∘ f → Any P ⋐ Any Q ∘ map f
  gmap g = map⁺ ∘ Any.map g

------------------------------------------------------------------------
-- mapMaybe

module _ (f : A → Maybe B) where

  mapMaybe⁺ : ∀ xs → Any (MAny.Any P) (map f xs) → Any P (mapMaybe f xs)
  mapMaybe⁺ (x ∷ xs) ps with f x | ps
  ... | nothing | there pxs      = mapMaybe⁺ xs pxs
  ... | just _  | here (just py) = here py
  ... | just _  | there pxs      = there (mapMaybe⁺ xs pxs)

------------------------------------------------------------------------
-- _++_

module _ {P : A → Set p} where

  ++⁺ˡ : Any P xs → Any P (xs ++ ys)
  ++⁺ˡ (here p)  = here p
  ++⁺ˡ (there p) = there (++⁺ˡ p)

  ++⁺ʳ : ∀ xs {ys} → Any P ys → Any P (xs ++ ys)
  ++⁺ʳ []       p = p
  ++⁺ʳ (x ∷ xs) p = there (++⁺ʳ xs p)

  ++⁻ : ∀ xs {ys} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  ++⁻ []       p         = inj₂ p
  ++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
  ++⁻ (x ∷ xs) (there p) = Sum.map there id (++⁻ xs p)

  ++⁺∘++⁻ : ∀ xs {ys} (p : Any P (xs ++ ys)) → [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs p) ≡ p
  ++⁺∘++⁻ []       p         = refl
  ++⁺∘++⁻ (x ∷ xs) (here  p) = refl
  ++⁺∘++⁻ (x ∷ xs) (there p) with ih ← ++⁺∘++⁻ xs p | ++⁻ xs p
  ... | inj₁ _ = cong there ih
  ... | inj₂ _ = cong there ih

  ++⁻∘++⁺ : ∀ xs {ys} (p : Any P xs ⊎ Any P ys) →
            ++⁻ xs ([ ++⁺ˡ , ++⁺ʳ xs ]′ p) ≡ p
  ++⁻∘++⁺ []            (inj₂ p)         = refl
  ++⁻∘++⁺ (x ∷ xs)      (inj₁ (here  p)) = refl
  ++⁻∘++⁺ (x ∷ xs) {ys} (inj₁ (there p)) rewrite ++⁻∘++⁺ xs {ys} (inj₁ p) = refl
  ++⁻∘++⁺ (x ∷ xs)      (inj₂ p)         rewrite ++⁻∘++⁺ xs      (inj₂ p) = refl

  ++↔ : ∀ {xs ys} → (Any P xs ⊎ Any P ys) ↔ Any P (xs ++ ys)
  ++↔ {xs = xs} = mk↔ₛ′ [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs) (++⁺∘++⁻ xs) (++⁻∘++⁺ xs)

  ++-comm : ∀ xs ys → Any P (xs ++ ys) → Any P (ys ++ xs)
  ++-comm xs ys = [ ++⁺ʳ ys , ++⁺ˡ ]′ ∘ ++⁻ xs

  ++-comm∘++-comm : ∀ xs {ys} (p : Any P (xs ++ ys)) →
                    ++-comm ys xs (++-comm xs ys p) ≡ p
  ++-comm∘++-comm [] {ys} p
    rewrite ++⁻∘++⁺ ys {ys = []} (inj₁ p) = refl
  ++-comm∘++-comm (x ∷ xs) {ys} (here p)
    rewrite ++⁻∘++⁺ ys {ys = x ∷ xs} (inj₂ (here p)) = refl
  ++-comm∘++-comm (x ∷ xs)      (there p) with ++⁻ xs p | ++-comm∘++-comm xs p
  ++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ʳ ys p))))
    | inj₁ p | refl
    rewrite ++⁻∘++⁺ ys (inj₂                 p)
          | ++⁻∘++⁺ ys (inj₂ $ there {x = x} p) = refl
  ++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ˡ p))))
    | inj₂ p | refl
    rewrite ++⁻∘++⁺ ys {ys =     xs} (inj₁ p)
          | ++⁻∘++⁺ ys {ys = x ∷ xs} (inj₁ p) = refl

  ++↔++ : ∀ xs ys → Any P (xs ++ ys) ↔ Any P (ys ++ xs)
  ++↔++ xs ys = mk↔ₛ′ (++-comm xs ys) (++-comm ys xs)
                        (++-comm∘++-comm ys) (++-comm∘++-comm xs)

  ++-insert : ∀ xs {ys} → P x → Any P (xs ++ [ x ] ++ ys)
  ++-insert xs Px = ++⁺ʳ xs (++⁺ˡ (singleton⁺ Px))

------------------------------------------------------------------------
-- concat

module _ {P : A → Set p} where

  concat⁺ : ∀ {xss} → Any (Any P) xss → Any P (concat xss)
  concat⁺ (here p)           = ++⁺ˡ p
  concat⁺ (there {x = xs} p) = ++⁺ʳ xs (concat⁺ p)

  concat⁻ : ∀ xss → Any P (concat xss) → Any (Any P) xss
  concat⁻ ([]       ∷ xss) p         = there $ concat⁻ xss p
  concat⁻ ((x ∷ xs) ∷ xss) (here  p) = here (here p)
  concat⁻ ((x ∷ xs) ∷ xss) (there p) with concat⁻ (xs ∷ xss) p
  ... | here  p′ = here (there p′)
  ... | there p′ = there p′

  concat⁻∘++⁺ˡ : ∀ {xs} xss (p : Any P xs) →
                 concat⁻ (xs ∷ xss) (++⁺ˡ p) ≡ here p
  concat⁻∘++⁺ˡ xss (here  p) = refl
  concat⁻∘++⁺ˡ xss (there p) rewrite concat⁻∘++⁺ˡ xss p = refl

  concat⁻∘++⁺ʳ : ∀ xs xss (p : Any P (concat xss)) →
                   concat⁻ (xs ∷ xss) (++⁺ʳ xs p) ≡ there (concat⁻ xss p)
  concat⁻∘++⁺ʳ []       xss p = refl
  concat⁻∘++⁺ʳ (x ∷ xs) xss p rewrite concat⁻∘++⁺ʳ xs xss p = refl

  concat⁺∘concat⁻ : ∀ xss (p : Any P (concat xss)) →
                      concat⁺ (concat⁻ xss p) ≡ p
  concat⁺∘concat⁻ ([]       ∷ xss) p         = concat⁺∘concat⁻ xss p
  concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (here p)  = refl
  concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there p)
    with p | concat⁻ (xs ∷ xss) p | concat⁺∘concat⁻ (xs ∷ xss) p
  ... | .(++⁺ˡ p′)              | here  p′ | refl = refl
  ... | .(++⁺ʳ xs (concat⁺ p′)) | there p′ | refl = refl

  concat⁻∘concat⁺ : ∀ {xss} (p : Any (Any P) xss) → concat⁻ xss (concat⁺ p) ≡ p
  concat⁻∘concat⁺ (here                      p) = concat⁻∘++⁺ˡ _ p
  concat⁻∘concat⁺ (there {x = xs} {xs = xss} p)
    rewrite concat⁻∘++⁺ʳ xs xss (concat⁺ p) =
      cong there $ concat⁻∘concat⁺ p

  concat↔ : ∀ {xss} → Any (Any P) xss ↔ Any P (concat xss)
  concat↔ {xss} = mk↔ₛ′ concat⁺ (concat⁻ xss) (concat⁺∘concat⁻ xss) concat⁻∘concat⁺

------------------------------------------------------------------------
-- concatMap

module _ (f : A → List B) {p} {P : Pred B p} where

  concatMap⁺ : Any (Any P ∘ f) xs → Any P (concatMap f xs)
  concatMap⁺ = concat⁺ ∘ map⁺

  concatMap⁻ : Any P (concatMap f xs) → Any (Any P ∘ f) xs
  concatMap⁻ = map⁻ ∘ concat⁻ _

------------------------------------------------------------------------
-- cartesianProductWith

module _ (f : A → B → C) where

  cartesianProductWith⁺ : (∀ {x y} → P x → Q y → R (f x y)) →
                          Any P xs → Any Q ys →
                          Any R (cartesianProductWith f xs ys)
  cartesianProductWith⁺ pres (here  px)  qys = ++⁺ˡ (map⁺ (Any.map (pres px) qys))
  cartesianProductWith⁺ pres (there qxs) qys = ++⁺ʳ _ (cartesianProductWith⁺ pres qxs qys)

  cartesianProductWith⁻ : (∀ {x y} → R (f x y) → P x × Q y) → ∀ xs ys →
                          Any R (cartesianProductWith f xs ys) →
                          Any P xs × Any Q ys
  cartesianProductWith⁻ resp (x ∷ xs) ys Rxsys with ++⁻ (map (f x) ys) Rxsys
  ... | inj₁ Rfxys = let Rxys = map⁻ Rfxys
    in here (proj₁ (resp (proj₂ (Any.satisfied Rxys)))) , Any.map (proj₂ ∘ resp) Rxys
  ... | inj₂ Rc    = let pxs , qys = cartesianProductWith⁻ resp xs ys Rc
    in there pxs , qys

------------------------------------------------------------------------
-- cartesianProduct

cartesianProduct⁺ : Any P xs → Any Q ys →
                    Any (P ⟨×⟩ Q) (cartesianProduct xs ys)
cartesianProduct⁺ = cartesianProductWith⁺ _,_ _,_

cartesianProduct⁻ : ∀ xs ys → Any (P ⟨×⟩ Q) (cartesianProduct xs ys) →
                    Any P xs × Any Q ys
cartesianProduct⁻ = cartesianProductWith⁻ _,_ id

------------------------------------------------------------------------
-- applyUpTo

applyUpTo⁺ : ∀ f {i n} → P (f i) → i < n → Any P (applyUpTo f n)
applyUpTo⁺ _ p z<s       = here p
applyUpTo⁺ f p (s<s i<n@(s≤s _)) =
  there (applyUpTo⁺ (f ∘ suc) p i<n)

applyUpTo⁻ : ∀ f {n} → Any P (applyUpTo f n) →
             ∃ λ i → i < n × P (f i)
applyUpTo⁻ f {suc n} (here p)  = zero , z<s , p
applyUpTo⁻ f {suc n} (there p) =
  let i , i<n , q = applyUpTo⁻ (f ∘ suc) p in suc i , s<s i<n , q

------------------------------------------------------------------------
-- applyDownFrom

applyDownFrom⁺ : ∀ f {i n} → P (f i) → i < n → Any P (applyDownFrom f n)
applyDownFrom⁺ f {i} {suc n} p (s≤s i≤n) with i ≡? n
... | yes refl = here p
... | no  i≢n  = there (applyDownFrom⁺ f p (≤∧≢⇒< i≤n i≢n))

applyDownFrom⁻ : ∀ f {n} → Any P (applyDownFrom f n) →
                 ∃ λ i → i < n × P (f i)
applyDownFrom⁻ f {suc n} (here p)  = n , ≤-refl , p
applyDownFrom⁻ f {suc n} (there p) =
  let i , i<n , q = applyDownFrom⁻ f p in i , m<n⇒m<1+n i<n , q

------------------------------------------------------------------------
-- tabulate

tabulate⁺ : ∀ {n} {f : Fin n → A} i → P (f i) → Any P (tabulate f)
tabulate⁺ zero    p = here p
tabulate⁺ (suc i) p = there (tabulate⁺ i p)

-- dsp: lemmas
-- dsp: end of lemmas
tabulate⁻ : ∀ {n} {f : Fin n → A} → Any P (tabulate f) → ∃ λ i → P (f i)
-- Base case: n = 0. Fin 0 has no elements, so tabulate f is the empty list. Any P [] has no proof, so the implication holds vacuously.
tabulate⁻ {n = zero} {f = f} p = (contradiction p ¬Any[])
-- Inductive case: n = k + 1. Assume the statement holds for k and every function Fin k → A. By tabulateSuc, the proof is a proof of Any P (f zero :: tabulate (f ∘ suc)).
-- Sub-case: the proof certifies P (f zero). Take the witness zero, so P (f zero) is exactly the given proof.
tabulate⁻ {n = suc k} {f = f} (here px) = (zero , px)
-- Sub-case: the proof is a proof of Any P (tabulate (f ∘ suc)). Apply the induction hypothesis tabulate⁻ to f ∘ suc to get j : Fin k with P ((f ∘ suc) j). Take the witness suc j, since (f ∘ suc) j = f (suc j) by definition of composition.
tabulate⁻ {n = suc k} {f = f} (there pxs) = (suc (tabulate⁻ pxs .proj₁) , tabulate⁻ pxs .proj₂)
