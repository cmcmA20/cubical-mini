{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Operations.Properties where

open import Meta.Prelude
open import Meta.Effect
open import Foundations.Base
open import Functions.Embedding

open import Data.Reflects as Reflects
open import Data.Nat.Order.Base
open import Data.Sum.Base as Sum
open import Data.Vec.Inductive.Base as Vec
open import Data.Vec.Inductive.Path
open import Data.Vec.Inductive.Correspondences.Unary.All
open import Data.Vec.Inductive.Membership

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  x y z w : A

-- replicate

replicate-all : (n : ℕ)
              → All (_＝ z) (replicate n z)
replicate-all  zero   = []
replicate-all (suc n) = refl ∷ replicate-all n

All-replicate : {n : ℕ} (xs : Vec A n)
              → All (_＝ z) xs
              → xs ＝ replicate n z
All-replicate {n = zero}  []       []      = refl
All-replicate {n = suc n} (x ∷ xs) (e ∷ a) = ap² {C = λ _ _ → Vec _ (suc _)} _∷_ e (All-replicate xs a)

replicate-inj : (n : ℕ)
              → 0 < n
              → Injective {A = A} (replicate n)
replicate-inj  zero   lt e = false! lt
replicate-inj (suc n) lt e = ∷-head-inj e

-- zip-with

∈-zip-with-l : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
               {n : ℕ} {f : A → B → C} {as : Vec A n} {bs : Vec B n} {x : A}
              → x ∈ as
              → Σ[ y ꞉ B ] (y ∈ bs) × (f x y ∈ zip-with f as bs)
∈-zip-with-l {n = suc n} {f} {as = a ∷ as} {bs = b ∷ bs} {x} x∈ =
  [ (λ x=a → b , hereᵥ refl , hereᵥ (ap (λ q → f q b) x=a))
  , (λ x∈′ →
        let (b , b∈ , fab∈) = ∈-zip-with-l {f = f} {as = as} x∈′ in
        b , thereᵥ b∈ , thereᵥ fab∈)
  ]ᵤ (∈ᵥ-uncons x∈)

∈-zip-with-r : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
               {n : ℕ} {f : A → B → C} {as : Vec A n} {bs : Vec B n} {y : B}
              → y ∈ bs
              → Σ[ x ꞉ A ] (x ∈ as) × (f x y ∈ zip-with f as bs)
∈-zip-with-r {n = suc n} {f} {as = a ∷ as} {bs = b ∷ bs} y∈ =
  [ (λ y=b → a , hereᵥ refl , hereᵥ (ap (f a) y=b))
  , (λ y∈′ →
        let (a , a∈ , fab∈) = ∈-zip-with-r {f = f} {as = as} y∈′ in
        a , thereᵥ a∈ , thereᵥ fab∈)
  ]ᵤ (∈ᵥ-uncons y∈)

zip-with-∈ : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
             {n : ℕ} {f : A → B → C} {as : Vec A n} {bs : Vec B n} {c : C}
           → c ∈ zip-with f as bs
           → Σ[ a ꞉ A ] Σ[ b ꞉ B ] ((a ∈ as) × (b ∈ bs) × (c ＝ f a b))
zip-with-∈ {n = suc n} {as = a ∷ as} {bs = b ∷ bs} c∈ =
  [ (λ ce → a , b , hereᵥ refl , hereᵥ refl , ce)
  , (λ c∈′ →
       let (a′ , b′ , a∈ , b∈ , ce) = zip-with-∈ {as = as} c∈′ in
       a′ , b′ , thereᵥ a∈ , thereᵥ b∈ , ce)
  ]ᵤ (∈ᵥ-uncons c∈)

zip-with-inj : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
               {n : ℕ} {f : A → B → C}
               {as xs : Vec A n} {bs ys : Vec B n}
             → (∀ {x y a b} → f x y ＝ f a b → (x ＝ a) × (y ＝ b))
             → zip-with f as bs ＝ zip-with f xs ys
             → (as ＝ xs) × (bs ＝ ys)
zip-with-inj {n = zero}  {as = []}     {xs = []}     {bs = []}     {ys = []}     inj e = refl , refl
zip-with-inj {n = suc n} {as = a ∷ as} {xs = x ∷ xs} {bs = b ∷ bs} {ys = y ∷ ys} inj e =
  let (axe , bye) = inj (∷-head-inj e)
      (ihax , ihby) = zip-with-inj inj (∷-tail-inj e)
    in
    ap² {C = λ _ _ → Vec _ _} _∷_ axe ihax
  , ap² {C = λ _ _ → Vec _ _} _∷_ bye ihby
