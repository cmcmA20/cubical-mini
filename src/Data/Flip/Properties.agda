{-# OPTIONS --safe #-}
module Data.Flip.Properties where

open import Foundations.Base
open import Foundations.Path

open import Data.Flip.Base

private variable
  ℓ ℓ′ : Level
  A B : 𝒰 ℓ
  R S : A → A → 𝒰 ℓ′
  x x′ y y′ z : A

flip-sym-involutive : {A : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′} {x y : A}
                      {f : Flip R x y}
                    → (f ⁻¹) ⁻¹ ＝ f
flip-sym-involutive {f = fwd x} = refl
flip-sym-involutive {f = bwd x} = refl
