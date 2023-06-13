{-# OPTIONS --safe #-}
module Correspondences.Nullary.Classical.Instances.Bind where

open import Foundations.Base

open import Meta.Bind

open import Correspondences.Nullary.Classical.Instances.Idiom public

instance
  Bind-Classically : Bind (eff Classically)
  Bind-Classically ._>>=_ ¬¬a mf ¬b = ¬¬a $ λ a → mf a ¬b

-- Usage
-- module _ where private
--   open import Correspondences.Nullary.Negation
--   open import Data.Sum.Base
--   import Data.Empty.Base as ⊥

--   private variable
--     A : Type

--   LEM : Classically $ A ⊎ (¬ A)
--   LEM z = z $ inr $ z ∘ inl

--   DNE : Classically (¬¬ A → A)
--   DNE = do
--     inl a ← LEM
--       where inr a → pure λ ¬¬a → ⊥.rec (¬¬a a)
--     pure λ _ → a
