{-# OPTIONS --safe #-}
module Correspondences.Nullary.Classical.Base where

open import Foundations.Base

open import Correspondences.Nullary.Negation

private variable
  ℓ : Level

infix 0 ¬¬_
¬¬_ : Type ℓ → Type ℓ
¬¬ A = ¬ ¬ A

Classical = ¬¬_
