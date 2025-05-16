{-# OPTIONS --safe --no-exact-split #-}
module Data.Maybe.Operations where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Maybe.Base as Maybe

private variable
  ℓ : Level
  A : Type ℓ
  xm : Maybe A

all : (A → Bool) → Maybe A → Bool
all p = Maybe.rec true p

any : (A → Bool) → Maybe A → Bool
any p = Maybe.rec false p

filter : (A → Bool) → Maybe A → Maybe A
filter p (just x) = if p x then just x else nothing
filter p  nothing = nothing
