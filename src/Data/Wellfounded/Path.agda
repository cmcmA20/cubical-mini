{-# OPTIONS --safe #-}
module Data.Wellfounded.Path where

open import Meta.Prelude

open import Data.Bool.Base
open import Data.Reflects.Base
open import Data.Wellfounded.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  _<_ : A → A → Type ℓ′
  x : A
  n : HLevel

opaque
  acc-is-prop : ∀ x → is-prop (Acc _<_ x)
  acc-is-prop x (acc s) (acc t) = ap acc $
    fun-ext λ y → fun-ext λ y<x → acc-is-prop y (s y y<x) (t y y<x)

instance opaque
  H-Level-Acc : ⦃ n ≥ʰ 1 ⦄ → H-Level n (Acc _<_ x)
  H-Level-Acc ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (acc-is-prop _)
  {-# OVERLAPPING H-Level-Acc #-}

instance
  Reflects-Acc-Path : {a b : Acc _<_ x} → Reflects (a ＝ b) true
  Reflects-Acc-Path = ofʸ prop!
