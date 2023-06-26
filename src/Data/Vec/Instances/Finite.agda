{-# OPTIONS --safe #-}
module Data.Vec.Instances.Finite where

open import Foundations.Base

open import Meta.Bind

open import Correspondences.Nullary.Finite.Bishop

open import Data.Product.Properties
open import Data.Vec.Base

open import Truncation.Propositional

-- TODO looks slow, check this later
-- instance
--   Finite-Vec : {ℓ : Level} {A : Type ℓ} {n : ℕ}
--              → ⦃ Finite A ⦄ → Finite (Vec A n)
--   Finite-Vec {A} {0} = {!!}
--   Finite-Vec {A} {1} = fin do
--     aeq ← enumeration {T = A}
--     pure $ {!!} ∙ₑ aeq
--   Finite-Vec {A} {suc (suc n)} ⦃ (A-fin) ⦄ = fin do
--     let w = Finite-× ⦃ A-fin ⦄ ⦃ Finite-Vecₓ ⦄
--     veq ← w .enumeration
--     pure $ (Vecₓ≃Vec ₑ⁻¹) ∙ₑ veq
