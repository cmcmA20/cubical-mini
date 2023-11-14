{-# OPTIONS --safe #-}
module Data.Empty.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Data.Unit.Base

open import Data.Empty.Base public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  n : HLevel

opaque
  unfolding is-of-hlevel
  absurd-is-contr : is-contr (⊥ → A)
  absurd-is-contr .fst ()
  absurd-is-contr .snd _ _ ()

instance
  H-Level-absurd : H-Level n (⊥ → A)
  H-Level-absurd = hlevel-basic-instance 0 absurd-is-contr

absurd-is-of-hlevel : ∀ n → is-of-hlevel n (⊥ → A)
absurd-is-of-hlevel n = hlevel n

instance
  decomp-hlevel-absurd : goal-decomposition (quote is-of-hlevel) (⊥ → A)
  decomp-hlevel-absurd = decomp (quote absurd-is-of-hlevel) (`level-same ∷ [])

universal : (⊥ → A) ≃ ⊤
universal = _ , is-contr→is-equiv absurd-is-contr ⊤-is-contr

¬-extₑ : ¬ A → ¬ B → A ≃ B
¬-extₑ ¬a _  .fst a = absurd (¬a a)
¬-extₑ _  ¬b .snd .equiv-proof b = absurd (¬b b)

¬-≃ : (A → B) → (B → A) → (¬ A) ≃ (¬ B)
¬-≃ ab ba = prop-extₑ! (_∘ ba) (_∘ ab)
