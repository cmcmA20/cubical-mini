{-# OPTIONS --safe #-}
module Data.Dec.Properties where

open import Foundations.Base hiding (_∙_)
open import Foundations.Equiv

open import Meta.Effect.Idiom
open import Meta.Groupoid
open import Meta.Search.HLevel

open import Truncation.Propositional as ∥-∥₁

open import Data.Empty.Properties
open import Data.Sum.Properties

open import Data.Dec.Base as Dec
open import Data.Dec.Path

private variable
  ℓ ℓ′ : Level
  A P : Type ℓ
  B : Type ℓ′

dec-∥-∥₁-equiv : ∥ Dec P ∥₁ ≃ Dec ∥ P ∥₁
dec-∥-∥₁-equiv = prop-extₑ!
  (∥-∥₁.rec! $ Dec.dmap pure ∥-∥₁.rec!)
  (Dec.rec (yes <$>_) $ pure ∘ no ∘ _∘ pure)

dec-≃ : A ≃ B → Dec A ≃ Dec B
dec-≃ eqv = dec-as-sum ∙ ⊎-ap (¬-≃ to from) eqv ∙ (dec-as-sum ⁻¹)
  where open Equiv eqv

module dec-≃ {ℓ} {ℓ′} {A} {B} e = Equiv (dec-≃ {ℓ} {ℓ′} {A} {B} e)
