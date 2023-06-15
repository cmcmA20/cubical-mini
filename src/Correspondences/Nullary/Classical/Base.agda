{-# OPTIONS --safe #-}
module Correspondences.Nullary.Classical.Base where

open import Foundations.Base

open import Data.Empty.Base

private variable
  ℓ : Level

infix 0 ¬¬_
¬¬_ : Type ℓ → Type ℓ
¬¬ A = ¬ ¬ A

Classical = ¬¬_
