{-# OPTIONS --safe #-}
module Correspondences.Classical where

open import Meta.Prelude

open import Meta.Effect.Bind

open import Correspondences.Base public

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥

private variable
  ℓ : Level
  A : Type ℓ

infixr 0 ¬¬_
¬¬_ : Type ℓ → Type ℓ
¬¬ A = ¬ ¬ A

opaque
  is-classical : Type ℓ → Type ℓ
  is-classical = ¬¬_

  is-classical-β : is-classical A → ¬¬ A
  is-classical-β = refl

  is-classical-η : ¬¬ A → is-classical A
  is-classical-η = refl

  is-classical-is-prop : is-prop (is-classical A)
  is-classical-is-prop = hlevel 1

  Classically : Type ℓ → Type ℓ
  Classically = is-classical

opaque
  unfolding is-classical
  instance
    Map-Classically : Map (eff Classically)
    Map-Classically .map = contra ∘ contra

    Idiom-Classically : Idiom (eff Classically)
    Idiom-Classically .pure = _&_
    Idiom-Classically ._<*>_ ¬¬f ¬¬a ¬b = ¬¬a (λ a → ¬¬f (λ f → ¬b (f a)))

    Bind-Classically : Bind (eff Classically)
    Bind-Classically ._>>=_ ¬¬a mf ¬b = ¬¬a $ λ a → mf a ¬b


Essentially-classical : Type ℓ → Type ℓ
Essentially-classical = ¬¬_ weakly-stable_

-- Usage
-- module _ where private
--   open import Data.Sum.Base

--   LEM : Classically $ A ⊎ (¬ A)
--   LEM = go where opaque
--     unfolding Classically
--     go : Classically $ A ⊎ (¬ A)
--     go z = z $ inr $ z ∘ inl

--   DNE : Classically (¬¬ A → A)
--   DNE = do
--     inl a ← LEM
--       where inr a → pure $ λ ¬¬a → ⊥.rec $ ¬¬a a
--     pure λ _ → a
