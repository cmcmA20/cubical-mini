{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.All where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Unit.Base
open import Data.List.Base
open import Data.List.Path
open import Data.Dec as Dec

private variable
  ℓ ℓᵃ : Level
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
  Code-All {xs = x ∷ xs} (px ∷ p) (qx ∷ q) = ep .Pathᵉ px qx × Code-All p q

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

instance opaque
  H-Level-All : ∀ {n} → {xs : List A} → ⦃ A-hl : ∀ {x} → H-Level n (P x) ⦄ → H-Level n (All P xs)
  H-Level-All {n} .H-Level.has-of-hlevel = all-is-of-hlevel _  (λ _ → hlevel n)
  {-# OVERLAPPING H-Level-All #-}

all-uncons : {x : A} {@0 xs : List A} → All P (x ∷ xs) → P x × All P xs
all-uncons (px ∷ pxs) = px , pxs

all-++ : {@0 xs : List A} → All P xs → All P ys → All P (xs ++ ys)
all-++ []         pys = pys
all-++ (px ∷ pxs) pys = px ∷ all-++ pxs pys

all-split : {xs : List A} → All P (xs ++ ys) → All P xs × All P ys
all-split {xs = []}      ps      = [] , ps
all-split {xs = x ∷ xs} (p ∷ ps) = first (p ∷_) (all-split ps)

all-++-left : {xs : List A} → All P (xs ++ ys) → All P xs
all-++-left = fst ∘ all-split

all-++-right : {xs : List A} → All P (xs ++ ys) → All P ys
all-++-right = snd ∘ all-split

all-map : {@0 xs : List A} → ∀ᴱ[ P ⇒ Q ] → All P xs → All Q xs
all-map     f []       = []
all-map {P} f (p ∷ ps) = f p ∷ all-map {P = P} f ps

all-zip-with : {@0 xs : List A} → ∀ᴱ[ P ⇒ Q ⇒ R ] → All P xs → All Q xs → All R xs
all-zip-with     f [] [] = []
all-zip-with {P} f (p ∷ ps) (q ∷ qs) = f p q ∷ all-zip-with {P = P} f ps qs

all? : {ℓ ℓ′ : Level} {A : Type ℓ} {P : A → Type ℓ′} → Decidable P → Decidable (λ (xs : List A) → All P xs)
all? P? {([])}   = yes []
all? P? {x ∷ xs} =
  Dec.dmap (_∷_ $ₜ²_)
           (λ { ¬ps (px ∷ ps) → ¬ps (px , ps) })
           (P? <,> all? P?)
