{-# OPTIONS --safe #-}
module Data.Unit.Base where

open import Foundations.Base
open import Foundations.HLevel.Base

open import Agda.Builtin.Unit public

private variable
  n : HLevel

opaque
  unfolding is-of-hlevel
  ⊤-is-contr : is-contr ⊤
  ⊤-is-contr .fst = tt
  ⊤-is-contr .snd tt = refl

instance
  ⊤-is-of-hlevel : ∀ {n} → is-of-hlevel n ⊤
  ⊤-is-of-hlevel = is-of-hlevel-+-left 0 _ ⊤-is-contr


record ⊤ω : Typeω where
  instance constructor ttω
