{-# OPTIONS --safe #-}
module Data.Empty.Properties where

open import Foundations.Base
open import Foundations.Equiv
open import Meta.Search.HLevel

open import Data.Empty.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

¬-extₑ : ¬ A → ¬ B → A ≃ B
¬-extₑ ¬a ¬b = iso→equiv 𝔯
  where
  𝔯 : Iso _ _
  𝔯 .fst              a = absurd (¬a a)
  𝔯 .snd .is-iso.inv  b = absurd (¬b b)
  𝔯 .snd .is-iso.rinv b = absurd (¬b b)
  𝔯 .snd .is-iso.linv a = absurd (¬a a)

¬-≃ : (A → B) → (B → A) → (¬ A) ≃ (¬ B)
¬-≃ ab ba = prop-extₑ! (λ na → na ∘ ba) λ nb → nb ∘ ab
