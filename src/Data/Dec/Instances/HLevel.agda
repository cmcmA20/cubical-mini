{-# OPTIONS --safe #-}
module Data.Dec.Instances.HLevel where

open import Foundations.Base
open import Data.List.Base
open import Meta.Reflection.HLevel

open import Data.Dec.Path public

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

instance
  H-Level-Dec : ⦃ hl : H-Level n A ⦄
              → H-Level n (Dec A)
  H-Level-Dec = hlevel-instance (Dec-is-of-hlevel _ (hlevel _))

  decomp-dec : hlevel-decomposition (Dec A)
  decomp-dec = decomp (quote Dec-is-of-hlevel) (`level ∷ `search ∷ [])
