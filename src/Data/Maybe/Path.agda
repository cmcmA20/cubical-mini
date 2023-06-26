{-# OPTIONS --safe #-}
module Data.Maybe.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.HLevel

open import Data.Empty.Base
open import Data.Sum.Path
open import Data.Unit.Base

open import Data.Maybe.Base public

private variable
  ℓ : Level
  A : Type ℓ
  x y : A

maybe-as-sum : Maybe A ≃ (⊤ ⊎ A)
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
  𝔯 .snd .is-iso.linv nothing = refl

maybe-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) A → is-of-hlevel (2 + n) (Maybe A)
maybe-is-of-hlevel n Ahl =
  is-of-hlevel-≃ (2 + n) maybe-as-sum
    (⊎-is-of-hlevel n hlevel! Ahl)

nothing≠just : ¬ nothing ＝ just x
nothing≠just = ⊎-disjoint ∘ ap (maybe-as-sum .fst)

just-inj : just x ＝ just y → x ＝ y
just-inj = inr-inj ∘ ap (maybe-as-sum .fst)
