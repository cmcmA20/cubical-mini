{-# OPTIONS --safe #-}
module Data.Unit.Base where

open import Foundations.Base
open import Foundations.HLevel.Base

open import Agda.Builtin.Unit
  renaming (⊤ to ⊤ₜ)
  public

instance
  ⊤-Type-small : ⊤-notation Type
  ⊤-Type-small .⊤ = ⊤ₜ
  {-# OVERLAPPING ⊤-Type-small #-}

  ⊤-Type : ∀ {ℓ} → ⊤-notation (Type ℓ)
  ⊤-Type .⊤ = Lift _ ⊤ₜ
  {-# INCOHERENT ⊤-Type #-}

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
