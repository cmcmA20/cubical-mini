{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Operations.Properties where

open import Meta.Prelude
open import Meta.Effect
open import Foundations.Base

open import Data.Sum.Base as Sum
open import Data.Vec.Inductive.Base as Vec
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
