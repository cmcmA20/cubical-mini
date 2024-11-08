{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.Vec.Inductive.Base as Vec
open import Data.Vec.Inductive.Instances.Container

private variable
  @0 n : ℕ
  ℓ : Level
  A B : Type ℓ

mapᵥ : (A → B) → Vec A n → Vec B n
mapᵥ f []       = []
mapᵥ f (x ∷ xs) = f x ∷ mapᵥ f xs

open Map ⦃ ... ⦄

instance
  Map-Vec : Map (eff (λ T → Vec T n))
  Map-Vec .map = mapᵥ

  Lawful-Map-Vec : {n : ℕ} → Lawful-Map (eff (λ T → Vec T n))
  Lawful-Map-Vec = Lawful-Map-AC (fun-ext ∘ go) where
    go : ∀{ℓa ℓb n} {A : 𝒰 ℓa} {B : 𝒰 ℓb} (f : A → B) (xs : Vec A n) → map f xs ＝ Map-AC-default .map f xs
    go {n = 0}     f [] = refl
    go {n = suc n} f (x ∷ xs) = f x ∷_ $ go f xs
