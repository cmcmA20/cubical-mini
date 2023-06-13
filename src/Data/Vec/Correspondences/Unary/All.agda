{-# OPTIONS --safe #-}
module Data.Vec.Correspondences.Unary.All where

open import Foundations.Base

open import Structures.Base

open import Correspondences.Nullary.Separated
open import Correspondences.Unary.Decidable

open import Data.Dec as Dec
open import Data.Vec.Base
open import Data.Vec.Correspondences.Unary.Any

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : Pred ℓ′ A
  x : A
  @0 m n : ℕ
  @0 xs ys : Vec A n

data All {ℓ ℓ′} {A : Type ℓ} (P : Pred ℓ′ A) : @0 Vec A n → Type (ℓ ⊔ ℓ′) where
  []  : All P []
  _∷_ : P x → All P xs → All P (x ∷ xs)

all-++ : {m : ℕ} {@0 xs : Vec A m} → All P xs → All P ys → All P (xs ++ ys)
all-++ {m = 0}     []         pys = pys
all-++ {m = suc _} (px ∷ pxs) pys = px ∷ all-++ pxs pys

all-++-left : {xs : Vec A m} → All P (xs ++ ys) → All P xs
all-++-left {xs = []}    _        = []
all-++-left {xs = _ ∷ _} (p ∷ ps) = p ∷ all-++-left ps

all-++-right : {xs : Vec A m} → All P (xs ++ ys) → All P ys
all-++-right {xs = []}    ps       = ps
all-++-right {xs = _ ∷ _} (_ ∷ ps) = all-++-right ps

all? : Decidable P → Decidable (λ xs → All P {n = n} xs)
all? P? []       = yes []
all? P? (x ∷ xs) =
  Dec.map (λ { (px , ps) → px ∷ ps })
          (λ { ¬ps (px ∷ ps) → ¬ps (px , ps) })
          (P? x ∧ᵈ all? P? xs)

-- ¬∃¬→∀¬ : ∀ xs → ¬ (Any P {n = n} xs) → All (¬_ ∘ P) xs
-- ¬∃¬→∀¬ []       _ = []
-- ¬∃¬→∀¬ (x ∷ xs) f = f ∘ here ∷ ¬∃¬→∀¬ xs (λ z → f (there z))
