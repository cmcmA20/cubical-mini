{-# OPTIONS --safe #-}
module Data.Maybe.Properties where

open import Meta.Prelude

open import Logic.Decidability

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
maybe-as-sum = ≅→≃ 𝔯
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

instance
  is-nothing-decision : Decidable (is-nothing x)
  is-nothing-decision {x = nothing} = yes tt
  is-nothing-decision {x = just _}  = no  refl

  is-just-decision : Decidable (is-just x)
  is-just-decision {x = nothing} = no  refl
  is-just-decision {x = just _}  = yes tt
