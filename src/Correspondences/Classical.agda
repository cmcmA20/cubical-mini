{-# OPTIONS --safe #-}
module Correspondences.Classical where

open import Foundations.Base

open import Meta.Bind

open import Correspondences.Base public

open import Data.Empty.Base

private variable
  ℓ : Level

infix 0 ¬¬_
¬¬_ : Type ℓ → Type ℓ
¬¬ A = ¬ ¬ A

opaque
  Classical : Type ℓ → Type ℓ
  Classical = ¬¬_

  Classically : Type ℓ → Type ℓ
  Classically = ¬¬_

  instance
    Map-Classically : Map (eff Classically)
    Map-Classically ._<$>_ f ¬¬a ¬b = ¬¬a λ a → ¬b (f a)

    Idiom-Classically : Idiom (eff Classically)
    Idiom-Classically .pure a ¬a = ¬a a
    Idiom-Classically ._<*>_ ¬¬f ¬¬a ¬b = ¬¬a (λ a → ¬¬f (λ f → ¬b (f a)))

    Bind-Classically : Bind (eff Classically)
    Bind-Classically ._>>=_ ¬¬a mf ¬b = ¬¬a $ λ a → mf a ¬b


-- Usage
-- module _ where private
--   open import Data.Sum.Base
--   import Data.Empty.Base as ⊥

--   private variable
--     A : Type

--   LEM : Classically $ A ⊎ (¬ A)
--   LEM = go where opaque
--     unfolding Classically
--     go : _
--     go z = z $ inr $ z ∘ inl

--   DNE : Classically (¬¬ A → A)
--   DNE = do
--     inl a ← LEM
--       where inr a → pure λ ¬¬a → ⊥.rec (¬¬a a)
--     pure λ _ → a
