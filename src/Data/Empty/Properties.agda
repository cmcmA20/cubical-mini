{-# OPTIONS --safe #-}
module Data.Empty.Properties where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel

open import Data.Unit.Base

open import Data.Empty.Base

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : ⊥ₜ → Type ℓᶜ
  n : HLevel

¬-is-equiv : {f : ¬ A} → is-equiv f
¬-is-equiv .equiv-proof ()

¬→≃⊥ : (¬ A) → A ≃ ⊥
¬→≃⊥ = _, ¬-is-equiv

absurd-is-contr : is-contr (Π[ f ꞉ ⊥ ] C f)
absurd-is-contr .fst ()
absurd-is-contr .snd _ _ ()

instance
  H-Level-absurd : H-Level n (Π[ f ꞉ ⊥ ] C f)
  H-Level-absurd = hlevel-basic-instance 0 absurd-is-contr
  {-# OVERLAPPING H-Level-absurd #-}

universal : (Π[ f ꞉ ⊥ ] C f) ≃ ⊤
universal = _ , is-contr→is-equiv absurd-is-contr ⊤-is-contr

¬-extₑ : ¬ A → ¬ B → A ≃ B
¬-extₑ ¬a ¬b = ¬→≃⊥ ¬a ∙ ¬→≃⊥ ¬b ⁻¹

¬-≃ : (A → B) → (B → A) → (¬ A) ≃ (¬ B)
¬-≃ ab ba = prop-extₑ! (_∘ ba) (_∘ ab)
