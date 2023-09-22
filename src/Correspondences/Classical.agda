{-# OPTIONS --safe #-}
module Correspondences.Classical where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind
open import Meta.Search.HLevel
open import Meta.Underlying

open import Correspondences.Base public

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Empty.Instances.HLevel

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
  is-classical-β = id

  is-classical-η : ¬¬ A → is-classical A
  is-classical-η = id

  is-classical-is-prop : is-prop (is-classical A)
  is-classical-is-prop = hlevel!

  Classically : Type ℓ → Type ℓ
  Classically = is-classical

opaque
  unfolding is-classical
  instance
    Map-Classically : Map (eff Classically)
    Map-Classically ._<$>_ f ¬¬a ¬b = ¬¬a $ ¬b ∘ f

    Idiom-Classically : Idiom (eff Classically)
    Idiom-Classically .pure = _&_
    Idiom-Classically ._<*>_ ¬¬f ¬¬a ¬b = ¬¬a (λ a → ¬¬f (λ f → ¬b (f a)))

    Bind-Classically : Bind (eff Classically)
    Bind-Classically ._>>=_ ¬¬a mf ¬b = ¬¬a $ λ a → mf a ¬b


opaque
  Essentially-classical : Type ℓ → Type ℓ
  Essentially-classical = ¬¬_ weakly-stable_

  essentially-classical-β : Essentially-classical A → ¬¬_ weakly-stable A
  essentially-classical-β = id

  essentially-classical-η : ¬¬_ weakly-stable A → Essentially-classical A
  essentially-classical-η = id

  is-essentially-classical : Prop ℓ → Prop ℓ
  is-essentially-classical A = el! (Essentially-classical ⌞ A ⌟)

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
--       where inr a → pure $ λ ¬¬a → ⊥.rec (¬¬a a)
--     pure λ _ → a
