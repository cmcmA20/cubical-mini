{-# OPTIONS --safe #-}
module Data.Vec.Instances.Finite where

open import Foundations.Base

open import Meta.Bind
open import Meta.Finite

open import Data.Vec.Base

open import Truncation.Propositional

-- TODO Vec ≃ Vecₓ
-- instance
--   Finite-Vec : {ℓ : Level} {A : Type ℓ} {n : ℕ}
--              → ⦃ Finite A ⦄ → Finite (Vec A n)
--   Finite-Vec {A} {n} = fin do
--     aeq ← enumeration {T = A}
--     pure {!!}
