{-# OPTIONS --safe #-}
module Data.Empty.Properties where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel

open import Data.Unit.Base

open import Data.Empty.Base public

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : ⊥ → Type ℓᶜ
  n : HLevel

opaque
  unfolding is-of-hlevel
  absurd-is-contr : is-contr (Π[ f ꞉ ⊥ ] C f)
  absurd-is-contr .fst ()
  absurd-is-contr .snd _ _ ()

instance
  H-Level-absurd : H-Level n (Π[ f ꞉ ⊥ ] C f)
  H-Level-absurd = hlevel-basic-instance 0 absurd-is-contr

universal : (Π[ f ꞉ ⊥ ] C f) ≃ ⊤
universal = _ , is-contr→is-equiv absurd-is-contr ⊤-is-contr

¬-extₑ : ¬ A → ¬ B → A ≃ B
¬-extₑ ¬a _  .fst a = absurd (¬a a)
¬-extₑ _  ¬b .snd .equiv-proof b = absurd (¬b b)

¬-≃ : (A → B) → (B → A) → (¬ A) ≃ (¬ B)
¬-≃ ab ba = prop-extₑ! (_∘ ba) (_∘ ab)
