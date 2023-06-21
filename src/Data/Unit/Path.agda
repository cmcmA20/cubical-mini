{-# OPTIONS --safe #-}
module Data.Unit.Path where

open import Foundations.Base

open import Data.Unit.Base public

opaque
  unfolding is-of-hlevel
  ⊤-is-contr : is-contr ⊤
  ⊤-is-contr .fst = tt
  ⊤-is-contr .snd tt = refl
