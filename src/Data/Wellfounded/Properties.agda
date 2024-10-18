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

Wf-on : (f : B → A)
      → Wf _<_ → Wf (λ x y → f x < f y)
Wf-on f wf x = Acc-on f x (wf (f x))

Noeth-on : (f : B → A)
         → Noeth _<_ → Noeth (λ x y → f x < f y)
Noeth-on f nth x = Acc-on f x (nth (f x))

FinHeight-on : (f : B → A)
             → FinHeight _<_ → FinHeight (λ x y → f x < f y)
FinHeight-on f fh x = Acc-on f x (fh (f x) .fst) , Acc-on f x (fh (f x) .snd)
