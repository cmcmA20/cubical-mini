{-# OPTIONS --safe #-}
module Data.Wellfounded.Properties where

open import Meta.Prelude

open import Data.Wellfounded.Base

private variable
  ℓa ℓb ℓ : Level
  A : 𝒰 ℓa
  B : 𝒰 ℓb
  _<_ : A → A → 𝒰 ℓ

Acc-on : (f : B → A) (b : B)
       → Acc _<_ (f b) → Acc (λ x y → f x < f y) b
Acc-on f b (acc rec) = acc λ y p → Acc-on f y (rec (f y) p)
