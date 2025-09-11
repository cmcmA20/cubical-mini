{-# OPTIONS --safe #-}
module Data.These.Properties where

open import Foundations.Base
import Data.Reflects.Base as Reflects
open import Data.Maybe.Base
open import Data.Maybe.Path
open import Data.These.Base

private variable
  ℓ ℓ′ ℓ″ ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  D : Type ℓᵈ

fromMaybe2-nothing : {ma : Maybe A} {mb : Maybe B}
                   → fromMaybe2 ma mb ＝ nothing
                   → (ma ＝ nothing) × (mb ＝ nothing)
fromMaybe2-nothing {ma = just _}  {mb = just _}  e = Reflects.false! e
fromMaybe2-nothing {ma = just _}  {mb = nothing} e = Reflects.false! e
fromMaybe2-nothing {ma = nothing} {mb = just _}  e = Reflects.false! e
fromMaybe2-nothing {ma = nothing} {mb = nothing} e = refl , refl
