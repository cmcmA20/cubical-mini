{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Correspondences.Unary.All where

open import Foundations.Base

open import Meta.Search.Decidable
open import Meta.Search.Discrete

open import Meta.Variadic

open import Structures.Base

open import Correspondences.Separated

open import Data.Dec as Dec
open import Data.Vec.Inductive.Base
open import Data.Vec.Inductive.Correspondences.Unary.Any

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

all-head : All P (x ∷ xs) → P x
all-head (u ∷ _) = u

all-tail : All P (x ∷ xs) → All P xs
all-tail (_ ∷ us) = us

-- FIXME `Decidable` macro dies here, why?
all? : Decidable P → Decidableⁿ {1} (λ (xs : Vec A n) → All P xs)
all? P? []       = yes []
all? P? (x ∷ xs) =
  Dec.dmap (λ { (px , ps) → px ∷ ps })
           (λ { ¬ps (px ∷ ps) → ¬ps (px , ps) })
           (×-decision (P? x) (all? P? xs))


instance
  all-is-discrete : {xs : Vec A n}
                  ⦃ di : ∀ {x} → is-discrete (P x) ⦄
                  → is-discrete (All P xs)
  all-is-discrete {xs = []} .is-discrete-β [] [] = yes refl
  all-is-discrete {P} {xs = xs@(_ ∷ _)} ⦃ di ⦄ .is-discrete-β (u ∷ us) (v ∷ vs) = Dec.dmap
    (λ (p , q) → ap² {C = λ _ _ → All P xs} _∷_ p q)
    (λ f p → f (ap all-head p , ap all-tail p))
    (×-decision (di .is-discrete-β u v)
                (all-is-discrete .is-discrete-β us vs))

private
  all-discrete-helper : {xs : Vec A n} (di : ∀ x → is-discrete (P x)) → is-discrete (All P xs)
  all-discrete-helper di = all-is-discrete ⦃ λ {x} → di x ⦄

instance
  decomp-all-dis : goal-decomposition (quote is-discrete) (All P xs)
  decomp-all-dis = decomp (quote all-discrete-helper) [ `search-under 1 (quote is-discrete) ]

-- ¬∃¬→∀¬ : ∀ xs → ¬ (Any P {n = n} xs) → All (¬_ ∘ P) xs
-- ¬∃¬→∀¬ []       _ = []
-- ¬∃¬→∀¬ (x ∷ xs) f = f ∘ here ∷ ¬∃¬→∀¬ xs (λ z → f (there z))
