{-# OPTIONS --safe #-}
module Correspondences.Nullary.DoubleNegation.Instances.Bind where

open import Foundations.Base

open import Meta.Bind

open import Correspondences.Nullary.DoubleNegation.Instances.Idiom public

instance
  Bind-¬¬ : Bind (eff ¬¬_)
  Bind-¬¬ .Bind._>>=_ ¬¬a mf ¬b = ¬¬a (λ a → mf a ¬b)

-- Usage

-- open import Data.Sum.Base
-- open import Data.Empty.Base

-- Classically = ¬¬_

-- LEM : Π[ A ꞉ Type ] Classically (A ⊎ (¬ A))
-- LEM A z = z (inr λ a → z (inl a))

-- DNE : Π[ A ꞉ Type ] Classically (¬¬ A → A)
-- DNE A = do
--   inl a ← LEM A
--     where inr a → pure λ ¬¬a → rec (¬¬a a)
--   pure $ const a
