{-# OPTIONS --safe #-}
module Data.Vec.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind
open import Meta.Search.Finite.Bishop

open import Data.Product.Properties
open import Data.Vec.Base

open import Truncation.Propositional

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

-- TODO
-- vec-is-fin-set : is-fin-set A → is-fin-set (Vec A n)
-- vec-is-fin-set {n = 0} _ = fin {n = 0} ∣ {!!} ∣₁
-- vec-is-fin-set {n = 1} fi = {!!}
-- vec-is-fin-set {n = suc (suc n)} fi = fin do
--   let w = ×-is-fin-set fi (vec-is-fin-set {n = suc n} fi)
--   e ← enumeration w
--   pure ({!!} ∙ₑ e)
