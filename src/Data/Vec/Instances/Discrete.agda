{-# OPTIONS --safe #-}
module Data.Vec.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.HLevel

open import Correspondences.Nullary.Decidable

open import Data.Dec.Base
open import Data.Vec.Base

instance
  Vec-is-discrete : {ℓ : Level} {A : Type ℓ} {n : ℕ}
                  → ⦃ is-discrete A ⦄ → is-discrete (Vec A n)
  Vec-is-discrete {A} {n} = is-discrete-η go where
    go : {n : ℕ} (x y : Vec A n) → Dec (x ＝ y)
    go []       []       = yes refl
    go (x ∷ xs) (y ∷ ys) with x ≟ y
    ... | no  x≠y = no λ p → x≠y (ap head p)
    ... | yes x＝y with go xs ys
    ... | no  xs≠ys  = no λ p → xs≠ys (ap tail p)
    ... | yes xs＝ys = yes (ap₂ _∷_ x＝y xs＝ys)
