{-# OPTIONS --safe #-}
module Data.Vec.Instances.Discrete where

open import Foundations.Base

open import Meta.Discrete
open import Meta.Reflection.HLevel

open import Data.Vec.Base

instance
  Discrete-Vec : {ℓ : Level} {A : Type ℓ} {n : ℕ}
               → ⦃ Discrete A ⦄ → Discrete (Vec A n)
  Discrete-Vec {A} {n} .Discrete._≟_ = go
    where
      go : {n : ℕ} → is-discrete (Vec A n)
      go []       []       = yes refl
      go (x ∷ xs) (y ∷ ys) with x ≟ y
      ... | no  x≠y = no λ p → x≠y (ap head p)
      ... | yes x＝y with go xs ys
      ... | no  xs≠ys  = no λ p → xs≠ys (ap tail p)
      ... | yes xs＝ys = yes (ap₂ _∷_ x＝y xs＝ys)
