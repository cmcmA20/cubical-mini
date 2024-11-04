{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Correspondences.Unary.All where

open import Meta.Prelude
open import Meta.Effect
open import Meta.Literals.FromProduct
open Variadics _

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Dec as Dec
open import Data.Vec.Inductive.Base
open import Data.Vec.Inductive.Instances.FromProduct
open import Data.Vec.Inductive.Correspondences.Unary.Any

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  P : Pred A ℓ′
  Q : Pred A ℓ″
  x : A
  @0 m n : ℕ
  @0 xs ys : Vec A n

infixr 5 _∷_
data All {ℓ ℓ′} {A : Type ℓ} (P : Pred A ℓ′) : @0 Vec A n → Type (ℓ ⊔ ℓ′) where
  []  : All P []
  _∷_ : P x → All P xs → All P (x ∷ xs)

instance
  From-prodᵈ-All
    : ∀{ℓ ℓ′} {A : Type ℓ} {P : A → Type ℓ′}
    → From-productᵈ P λ xs → All P xs
  From-prodᵈ-All {A} {P} .from-prodᵈ = go where
    go : (n : ℕ) (xs : Prod A n) (ds : Prodᵈ P xs) → All P (from-prod n xs)
    go 0 _ _ = []
    go 1 _ p = p ∷ []
    go (suc (suc n)) (x , xs) (p , ps) = p ∷ go (suc n) xs ps

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

all-map : {n : ℕ} {@0 xs : Vec A n} → ∀[ P ⇒ Q ] → All P xs → All Q xs
all-map {n = 0}     _ []       = []
all-map {n = suc n} f (p ∷ ps) = f p ∷ all-map f ps

all? : Decidable P → Decidable (λ (xs : Vec A n) → All P xs)
all? P? {([])}   = yes []
all? P? {x ∷ xs} =
  Dec.dmap (λ { (px , ps) → px ∷ ps })
           (λ { ¬ps (px ∷ ps) → ¬ps (px , ps) })
           (P? <,> all? P?)

instance
  all-is-discrete : {xs : Vec A n}
                    ⦃ di : ∀ {x} → is-discrete (P x) ⦄
                  → is-discrete (All P xs)
  all-is-discrete {xs = []} {([])} {([])} = yes refl
  all-is-discrete {P} {xs = xs@(_ ∷ _)} ⦃ di ⦄ {u ∷ us} {v ∷ vs} = Dec.dmap
    (λ (p , q) → ap² {C = λ _ _ → All P xs} _∷_ p q)
    (λ f p → f (ap all-head p , ap all-tail p))
    (u ≟ v <,> all-is-discrete)

-- ¬∃¬→∀¬ : ∀ xs → ¬ (Any P {n = n} xs) → All (¬_ ∘ P) xs
-- ¬∃¬→∀¬ []       _ = []
-- ¬∃¬→∀¬ (x ∷ xs) f = f ∘ here ∷ ¬∃¬→∀¬ xs (λ z → f (there z))
