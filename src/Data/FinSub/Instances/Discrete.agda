{-# OPTIONS --safe #-}
module Data.FinSub.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Dec.Base as Dec
open import Data.Nat.Instances.Discrete

open import Data.FinSub.Base

instance
  fin-is-discrete : ∀ {n} → is-discrete (Fin n)
  fin-is-discrete = is-discrete-η λ k l → Dec.map
    fin-ext (λ k≠l p → k≠l (ap Fin.index p)) (Fin.index k ≟ Fin.index l)
