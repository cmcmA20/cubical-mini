{-# OPTIONS --safe #-}
module Data.Sum.Exclusive.Instances.Finite where

open import Meta.Prelude

open import Meta.Effect.Bind

open import Combinatorics.Finiteness.Bishop.Manifest
open import Combinatorics.Finiteness.Bishop.Weak

open import Data.Fin.Computational.Closure
open import Data.Sum.Exclusive.Base
open import Data.Sum.Exclusive.Properties
open import Data.Truncation.Propositional.Instances.Bind

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

-- TODO
-- instance
--   ⊻-manifest-bishop-finite
--     : ⦃ A-mbf : Manifest-bishop-finite A ⦄ ⦃ B-mbf : Manifest-bishop-finite B ⦄
--     → Manifest-bishop-finite (A ⊻ B)
--   ⊻-manifest-bishop-finite = finite $ ⊻-ap (enumeration auto) (enumeration auto) ∙ {!!}
--   {-# OVERLAPPING ⊻-manifest-bishop-finite #-}

--   ⊻-is-bishop-finite
--     : ⦃ A-bf : is-bishop-finite A ⦄ → ⦃ B-bf : is-bishop-finite B ⦄
--     → is-bishop-finite (A ⊻ B)
--   ⊻-is-bishop-finite = finite₁ do
--     aeq ← enumeration₁ auto
--     beq ← enumeration₁ auto
--     pure $ ⊻-ap aeq beq ∙ {!!}
--   {-# OVERLAPPING ⊻-is-bishop-finite #-}
