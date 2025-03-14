{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.All where

open import Meta.Prelude
open import Meta.Effect
open import Meta.Extensionality
open Variadics _
open import Foundations.Sigma

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Empty.Base
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Reflects.Base as Reflects
open import Data.Reflects.Properties
open import Data.Sum.Base
open import Data.List.Base
open import Data.List.Path
open import Data.List.Instances.Map
open import Data.List.Operations

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  P Q R : Pred A ℓ
  x : A
  @0 xs ys : List A

infixr 5 _∷_
data All {ℓ ℓᵃ} {A : Type ℓᵃ} (P : Pred A ℓ) : @0 List A → Type (ℓ ⊔ ℓᵃ) where
  []  : All P []
  _∷_ : P x → All P xs → All P (x ∷ xs)

module _ {A : 𝒰 ℓᵃ} {P : Pred A ℓ} ⦃ ep : {a : A} → Extensional (P a) ℓ ⦄ where
  Code-All : {xs : List A} (p q : All P xs) → 𝒰 ℓ
  Code-All {xs = []}     []       []       = ⊤
  Code-All {xs = x ∷ xs} (px ∷ p) (qx ∷ q) = ep .Pathᵉ px qx ×ₜ Code-All p q

  code-all-refl : {xs : List A} (p : All P xs) → Code-All p p
  code-all-refl {xs = []}     []       = _
  code-all-refl {xs = x ∷ xs} (px ∷ p) = ep .reflᵉ px , code-all-refl p

  decode-all : {xs : List A} {p q : All P xs} (c : Code-All p q) → p ＝ q
  decode-all {xs = []}     {p = []}     {q = []}      _       = refl
  decode-all {xs = x ∷ xs} {p = px ∷ p} {q = qx ∷ q} (cx , c) =
    ap² {C = λ _ _ → All P (x ∷ xs)} _∷_ (ep .idsᵉ .to-path cx) (decode-all c)

  decode-all-refl : {xs : List A} {p q : All P xs} (c : Code-All p q)
                  → code-all-refl p ＝[ ap (Code-All p) (decode-all c) ]＝ c
  decode-all-refl {xs = []}     {p = []}     {q = []}     (lift tt) = refl
  decode-all-refl {xs = x ∷ xs} {p = px ∷ p} {q = qx ∷ q} (cx , c)  =
    ep .idsᵉ .to-path-over cx ,ₚ decode-all-refl c

  Extensional-All : {xs : List A} → Extensional (All P xs) ℓ
  Extensional-All .Pathᵉ              = Code-All
  Extensional-All .reflᵉ              = code-all-refl
  Extensional-All .idsᵉ .to-path      = decode-all
  Extensional-All .idsᵉ .to-path-over = decode-all-refl

-- this can be strengthened by requiring the hlevel of P only on x such that x ∈ₗ xs
opaque
  code-all-is-of-hlevel
    : ∀ {n} {xs : List A} {u v : All P xs}
    → (∀ x → is-of-hlevel (suc n) (P x))
    → is-of-hlevel n (Code-All u v)
  code-all-is-of-hlevel {n} {xs = []}     {u = []}     {v = []}     hl = hlevel n
  code-all-is-of-hlevel {n} {xs = x ∷ xs} {u = ux ∷ u} {v = vx ∷ v} hl =
    ×-is-of-hlevel n (path-is-of-hlevel n (hl x) ux vx) (code-all-is-of-hlevel hl)

all-is-contr
    : {xs : List A}
    → (∀ x → is-contr (P x))
    → is-contr (All P xs)
all-is-contr     {xs = []}     cntr = [] , λ where [] → refl
all-is-contr {P} {xs = x ∷ xs} cntr =
  let (xc , xeq) = cntr x
      (ac , aeq) = all-is-contr {xs = xs} cntr
    in
    xc ∷ ac
  , λ where (px ∷ pxs) → ap² {C = λ _ _ → All P (x ∷ xs)} _∷_ (xeq px) (aeq pxs)

all-is-of-hlevel
  : (n : HLevel) {xs : List A}
  → (∀ x → is-of-hlevel n (P x))
  → is-of-hlevel n (All P xs)
all-is-of-hlevel  zero   hl = all-is-contr hl
all-is-of-hlevel (suc n) hl =
  identity-system→is-of-hlevel n (Extensional-All .idsᵉ) (λ x y → code-all-is-of-hlevel hl)

instance
  H-Level-All : ∀ {n} {xs : List A} → ⦃ A-hl : ∀ {x} → H-Level n (P x) ⦄ → H-Level n (All P xs)
  H-Level-All {n} .H-Level.has-of-hlevel = all-is-of-hlevel _ (λ _ → hlevel n)
  {-# OVERLAPPING H-Level-All #-}

all-uncons : All P (x ∷ xs) → P x × All P xs
all-uncons (x ∷ xs) = x , xs

all-×≃ : All P (x ∷ xs) ≃ P x × All P xs
all-×≃ =
  ≅→≃ $
  make-iso all-uncons (_∷_ $²_) $
  make-inverses
    (fun-ext λ where (px , ax) → refl)
    (fun-ext λ where (px ∷ ax) → refl)

all-head : All P (x ∷ xs) → P x
all-head (x ∷ _) = x

all-tail : All P (x ∷ xs) → All P xs
all-tail (_ ∷ xs) = xs

¬all-∷ : {x : A} {xs : List A}
       → (¬ P x) ⊎ (¬ All P xs) → ¬ All P (x ∷ xs)
¬all-∷ (inl npx)  (px ∷ pxs) = npx px
¬all-∷ (inr npxs) (px ∷ pxs) = npxs pxs

all-++ : {@0 xs : List A} → All P xs → All P ys → All P (xs ++ ys)
all-++ []         pys = pys
all-++ (px ∷ pxs) pys = px ∷ all-++ pxs pys

all-split : {xs : List A} → All P (xs ++ ys) → All P xs × All P ys
all-split {xs = []}      ps      = [] , ps
all-split {xs = x ∷ xs} (p ∷ ps) = first (p ∷_) (all-split ps)

all-split-++ : {xs ys : List A} {axs : All P xs} {ays : All P ys}
             → all-split (all-++ axs ays) ＝ (axs , ays)
all-split-++ {xs = []}     {axs = []}             = refl
all-split-++ {xs = x ∷ xs} {axs = ax ∷ axs} {ays} =
  let ih = all-split-++ {axs = axs} {ays = ays} in
  ×-path (ap (ax ∷_) (ap fst ih)) (ap snd ih)

all-++-split : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xs ys : List A} {axys : All P (xs ++ ys)}
             → let (axs , ays) = all-split {xs = xs} axys in
               all-++ axs ays ＝ axys
all-++-split {xs = []}                        = refl
all-++-split {xs = x ∷ xs} {axys = ax ∷ axys} =
  ap (ax ∷_) (all-++-split {xs = xs} {axys = axys})

all-++≃ : {xs ys : List A} → All P (xs ++ ys) ≃ All P xs × All P ys
all-++≃ {xs} =
  ≅→≃ $
  make-iso all-split (all-++ $²_) $
  make-inverses
   (fun-ext λ where (axs , ays) → all-split-++)
   (fun-ext λ axys → all-++-split {xs = xs})

all-++-left : {xs : List A} → All P (xs ++ ys) → All P xs
all-++-left = fst ∘ all-split

all-++-right : {xs : List A} → All P (xs ++ ys) → All P ys
all-++-right = snd ∘ all-split

all-map : {@0 xs : List A} → ∀[ P ⇒ Q ] → All P xs → All Q xs
all-map     f []       = []
all-map {P} f (p ∷ ps) = f p ∷ all-map f ps

all→map : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {S : Pred B ℓ′} {f : A → B} {xs : List A}
        → All (S ∘ f) xs → All S (map f xs)
all→map {xs = []}     []        = []
all→map {xs = x ∷ xs} (sfx ∷ a) = sfx ∷ all→map a

all→zip : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {P : Pred A ℓ′} {Q : Pred B ℓ′} {xs : List A}  {ys : List B}
        → All P xs → All Q ys
        → All (λ x → P (x .fst) × Q (x .snd)) (zip xs ys)
all→zip {xs = []}     {ys = []}      ax        ay       = []
all→zip {xs = []}     {ys = y ∷ ys}  ax        ay       = []
all→zip {xs = x ∷ xs} {ys = []}      ax        ay       = []
all→zip {xs = x ∷ xs} {ys = y ∷ ys} (px ∷ ax) (qy ∷ ay) = (px , qy) ∷ all→zip ax ay

all←map : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {S : Pred B ℓ′} {f : A → B} {xs : List A}
        → All S (map f xs) → All (S ∘ f) xs
all←map {xs = []}     []        = []
all←map {xs = x ∷ xs} (sfx ∷ a) = sfx ∷ all←map a

all-zip-with : {@0 xs : List A} → ∀ᴱ[ P ⇒ Q ⇒ R ] → All P xs → All Q xs → All R xs
all-zip-with     f [] [] = []
all-zip-with {P} f (p ∷ ps) (q ∷ qs) = f p q ∷ all-zip-with {P = P} f ps qs

all-trivial : (∀ x → P x) → {xs : List A} → All P xs
all-trivial pt {xs = []}     = []
all-trivial pt {xs = x ∷ xs} = pt x ∷ all-trivial pt

-- reflection

Reflects-all : {xs : List A} {P : A → 𝒰 ℓ′} {p : A → Bool}
             → (∀ x → Reflects (P x) (p x))
             → Reflects (All P xs) (all p xs)
Reflects-all {xs = []}     rp = ofʸ []
Reflects-all {xs = x ∷ xs} rp =
  ≃→reflects (all-×≃ ⁻¹) (Reflects-× ⦃ rp = rp x ⦄ ⦃ rq = Reflects-all {xs = xs} rp ⦄)

Reflects-all-bool : {p : A → Bool} {xs : List A}
                  → Reflects (All (So ∘ p) xs) (all p xs)
Reflects-all-bool = Reflects-all λ x → Reflects-So
