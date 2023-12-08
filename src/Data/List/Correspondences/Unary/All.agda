{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.All where

open import Prelude
open import Correspondences.Base
open import Correspondences.Decidable
open import Data.List.Base
open import Data.Dec as Dec

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P Q R : Pred A ℓ′
  x : A
  @0 xs ys : List A

data All {ℓ ℓ′} {A : Type ℓ} (P : Pred A ℓ′) : @0 List A → Type (ℓ ⊔ ℓ′) where
  []  : All P []
  _∷_ : P x → All P xs → All P (x ∷ xs)

all-++ : {@0 xs : List A} → All P xs → All P ys → All P (xs ++ ys)
all-++ []         pys = pys
all-++ (px ∷ pxs) pys = px ∷ all-++ pxs pys

all-split : {xs : List A} → All P (xs ++ ys) → All P xs × All P ys
all-split {xs = []}      ps      = [] , ps
all-split {xs = x ∷ xs} (p ∷ ps) =
  let xps , yps = all-split {xs = xs} ps in (p ∷ xps) , yps

all-++-left : {xs : List A} → All P (xs ++ ys) → All P xs
all-++-left = fst ∘ all-split

all-++-right : {xs : List A} → All P (xs ++ ys) → All P ys
all-++-right = snd ∘ all-split

all-map : {@0 xs : List A} → ({@0 x : A} -> P x -> Q x) -> All P xs -> All Q xs
all-map     f []       = []
all-map {P} f (p ∷ ps) = f p ∷ all-map {P = P} f ps

all-zipwith : {@0 xs : List A} → ({@0 x : A} -> P x -> Q x → R x) -> All P xs -> All Q xs -> All R xs
all-zipwith     f [] [] = []
all-zipwith {P} f (p ∷ ps) (q ∷ qs) = f p q ∷ all-zipwith {P = P} f ps qs

-- FIXME what's going on with n-ary macro
all? : {ℓ ℓ′ : Level} {A : Type ℓ} {P : A → Type ℓ′} → Decidable P → Decidableⁿ {1} (λ (xs : List A) → All P xs)
all? P? []       = yes []
all? P? (x ∷ xs) =
  Dec.dmap (_∷_ $²_)
           (λ { ¬ps (px ∷ ps) → ¬ps (px , ps) })
           (×-decision (P? x) (all? P? xs))
