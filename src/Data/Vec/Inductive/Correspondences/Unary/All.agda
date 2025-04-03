{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Correspondences.Unary.All where

open import Meta.Prelude
open import Meta.Effect
open import Meta.Literals.FromProduct
open Variadics _
open import Foundations.Sigma

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Bool
open import Data.Reflects.Base as Reflects
open import Data.Reflects.Properties
open import Data.Dec as Dec
open import Data.Vec.Inductive.Base
open import Data.Vec.Inductive.Operations
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

all-uncons : All P (x ∷ xs) → P x × All P xs
all-uncons (x ∷ xs) = x , xs

all-×≃ : All P (x ∷ xs) ≃ P x × All P xs
all-×≃ =
  ≅→≃ $
  make-iso all-uncons (_∷_ $²_) $
  make-inverses
    (fun-ext λ where (px , ax) → refl)
    (fun-ext λ where (px ∷ ax) → refl)

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

-- reflection

Reflects-all : {xs : Vec A n} {P : A → 𝒰 ℓ′} {p : A → Bool}
             → (∀ x → Reflects (P x) (p x))
             → Reflects (All P xs) (all p xs)
Reflects-all {xs = []}     rp = ofʸ []
Reflects-all {xs = x ∷ xs} rp =
  ≃→reflects (all-×≃ ⁻¹) (Reflects-× ⦃ rp = rp x ⦄ ⦃ rq = Reflects-all {xs = xs} rp ⦄)

Dec-all : {P : A → 𝒰 ℓ′} {xs : Vec A n}
        → (∀ x → Dec (P x))
        → Dec (All P xs)
Dec-all {xs} d .does  = all (λ x → d x .does) xs
Dec-all      d .proof = Reflects-all λ x → d x .proof

Reflects-all-bool : {p : A → Bool} {xs : Vec A n}
                  → Reflects (All (So ∘ p) xs) (all p xs)
Reflects-all-bool = Reflects-all λ x → Reflects-So

Dec-all-bool : ∀ {p : A → Bool} {xs : Vec A n}
             → Dec (All (So ∘ p) xs)
Dec-all-bool {p} {xs} .does  = all p xs
Dec-all-bool          .proof = Reflects-all-bool

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
