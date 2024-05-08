{-# OPTIONS --safe #-}
module Data.Unit.Base where

open import Foundations.Base
open import Foundations.HLevel.Base

open import Agda.Builtin.Unit public

private variable
  n : HLevel

⊤-is-contr : is-contr ⊤
⊤-is-contr .fst = tt
⊤-is-contr .snd _ = refl

instance
  H-Level-⊤ : H-Level n ⊤
  H-Level-⊤ = hlevel-basic-instance 0 ⊤-is-contr
  {-# OVERLAPPING H-Level-⊤ #-}

  H-Level-Path-⊤ : {x y : ⊤} → H-Level n (x ＝ y)
  H-Level-Path-⊤ = hlevel-basic-instance 0 (refl , λ _ → refl)
  {-# OVERLAPPING H-Level-Path-⊤ #-}


record ⊤ω : Typeω where
  instance constructor ttω
