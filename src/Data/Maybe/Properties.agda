{-# OPTIONS --safe #-}
module Data.Maybe.Properties where

open import Meta.Prelude

open import Logic.Decidability

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Maybe.Base public
open import Data.Maybe.Path
open import Data.Sum.Base
open import Data.Unit.Base

private variable
  ℓ : Level
  A : Type ℓ
  x : Maybe A

maybe-as-sum : Maybe A ≃ (⊤ ⊎ A)
maybe-as-sum = ≅→≃ i
  where
  i : Iso _ _
  i .fst (just x) = inr x
  i .fst nothing  = inl tt
  i .snd .is-iso.inv (inl _) = nothing
  i .snd .is-iso.inv (inr x) = just x
  i .snd .is-iso.rinv (inl _) = refl
  i .snd .is-iso.rinv (inr _) = refl
  i .snd .is-iso.linv (just _) = refl
  i .snd .is-iso.linv nothing  = refl

fibre-just : (m : Maybe A) ⦃ _ : So (is-just? m) ⦄ → fibre just m
fibre-just (just x) = x , refl
