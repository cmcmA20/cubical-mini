{-# OPTIONS --guarded #-}
module Data.Delay.Base where

open import Foundations.Base
open import Foundations.Prim.Delay

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

▹_ : Type ℓ → Type ℓ
▹ A = (@tick _ : Clock) → A

▸_ : ▹ Type ℓ → Type ℓ
▸ A = (@tick χ : Clock) → A χ

-- this is like a `♯_`
next : A → ▹ A
next x _ = x

postulate
  dfix      : (▹ A → A) → ▹ A
  dfix-path : (f : ▹ A → A) → dfix f ＝ next (f (dfix f))

{-# FOREIGN GHC import Data.Function #-}
{-# COMPILE GHC dfix = \ _ _ f -> fix (\ g _ -> f g) #-}

dfix-path′ : (f : ▹ A → A) → ▸ λ χ → dfix f χ ＝ f (dfix f)
dfix-path′ f χ i = dfix-path f i χ

fix : (▹ A → A) → A
fix f = f (dfix f)

fix-path : (f : ▹ A → A) → fix f ＝ f (next (fix f))
fix-path f = ap f (dfix-path f)

_<*>_ : ▹ (A → B) → ▹ A → ▹ B
_<*>_ lf lx χ = lf χ (lx χ)

map : (A → B) → ▹ A → ▹ B
map f lx χ = f (lx χ)
