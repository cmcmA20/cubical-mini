{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.All where

open import Foundations.Base

open import Correspondences.Base
open import Correspondences.Unary.Decidable

import      Data.Dec as Dec
open import Data.Dec
open import Data.List.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : Pred ℓ′ A
  x : A
  @0 xs ys : List A

data All {ℓ ℓ′} {A : Type ℓ} (P : Pred ℓ′ A) : @0 List A → Type (ℓ ⊔ ℓ′) where
  []  : All P []
  _∷_ : P x → All P xs → All P (x ∷ xs)

all-++ : All P xs → All P ys → All P (xs ++ ys)
all-++ []        ys = ys
all-++ (px ∷ ps) ys = px ∷ all-++ ps ys

all-++-left : {xs : List A} → All P (xs ++ ys) → All P xs
all-++-left {xs = []}    _        = []
all-++-left {xs = _ ∷ _} (p ∷ ps) = p ∷ all-++-left ps

all-++-right : {xs : List A} → All P (xs ++ ys) → All P ys
all-++-right {xs = []}    ps       = ps
all-++-right {xs = _ ∷ _} (_ ∷ ps) = all-++-right ps

all? : Decidable P → Decidable (λ xs → All P xs)
all? P? []       = yes []
all? P? (x ∷ xs) =
  Dec.map (λ { (px , ps) → px ∷ ps })
          (λ { ¬ps (px ∷ ps) → ¬ps (px , ps) })
          (P? x ∧ᵈ all? P? xs)
