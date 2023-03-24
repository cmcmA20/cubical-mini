{-# OPTIONS --safe #-}
module Cubical.Interface.Finite.TypeFormers where

open import Cubical.Foundations.Prelude

-- open import Cubical.Data.FinSet.Constructors
-- 
-- open import Cubical.Interface.Finite.Base
-- 
-- open Finite ⦃ ... ⦄
-- 
-- private variable
--   ℓ ℓ′ : Level
--   A : Type ℓ
--   B : A → Type ℓ′
-- 
-- instance
--   @0 FiniteΠ : ⦃ Finite A ⦄ → ⦃ {a : A} → Finite (B a) ⦄
--              → Finite ((a : A) → B a)
--   Finite.isFinite (FiniteΠ {A = A} {B = B}) = isFinSetΠ (A , isFinite) (λ a → B a , isFinite)
-- 
--   -- @0 FiniteLift : ⦃ Al : Finite A ⦄ → Finite (Lift {ℓ} {ℓ′} A)
--   -- FiniteLift = {!!}
