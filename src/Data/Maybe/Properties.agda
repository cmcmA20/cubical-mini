{-# OPTIONS --safe #-}
module Data.Maybe.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Maybe.Base public
open import Data.Sum.Base
open import Data.Unit.Base

maybe-as-sum : ∀{ℓ} {A : Type ℓ} → Maybe A ≃ (⊤ ⊎ A)
maybe-as-sum = iso→equiv 𝔯
  where
  𝔯 : Iso _ _
  𝔯 .fst (just x) = inr x
  𝔯 .fst nothing  = inl tt
  𝔯 .snd .is-iso.inv (inl _) = nothing
  𝔯 .snd .is-iso.inv (inr x) = just x
  𝔯 .snd .is-iso.rinv (inl _) = refl
  𝔯 .snd .is-iso.rinv (inr _) = refl
  𝔯 .snd .is-iso.linv (just _) = refl
  𝔯 .snd .is-iso.linv nothing  = refl
