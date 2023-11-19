{-# OPTIONS --safe #-}
module Data.Vec.Correspondences.Unary.All where

open import Foundations.Base

open import Meta.Search.Decidable
open import Meta.Variadic

open import Structures.Base

open import Correspondences.Decidable
open import Correspondences.Separated

open import Data.Dec as Dec
open import Data.Vec.Base
open import Data.Vec.Correspondences.Unary.Any.Inductive

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : Pred A ℓ′
  x : A
  @0 m n : ℕ
  @0 xs ys : Vec A n

data All {ℓ ℓ′} {A : Type ℓ} (P : Pred A ℓ′) : @0 Vec A n → Type (ℓ ⊔ ℓ′) where
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

-- FIXME `Decidable` macro dies here, why?
all? : Decidable P → Decidableⁿ {1} (λ (xs : Vec A n) → All P xs)
all? P? []       = yes []
all? P? (x ∷ xs) =
  Dec.map (λ { (px , ps) → px ∷ ps })
          (λ { ¬ps (px ∷ ps) → ¬ps (px , ps) })
          (×-decision (P? x) (all? P? xs))

-- ¬∃¬→∀¬ : ∀ xs → ¬ (Any P {n = n} xs) → All (¬_ ∘ P) xs
-- ¬∃¬→∀¬ []       _ = []
-- ¬∃¬→∀¬ (x ∷ xs) f = f ∘ here ∷ ¬∃¬→∀¬ xs (λ z → f (there z))
