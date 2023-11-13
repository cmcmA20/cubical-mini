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
  H-Level-⊤ : H-Level n ⊤
  H-Level-⊤ = hlevel-basic-instance 0 ⊤-is-contr


record ⊤ω : Typeω where
  instance constructor ttω
