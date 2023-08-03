{-# OPTIONS --safe #-}
module Foundations.Sigma where

open import Data.String.Base
open import Foundations.Base
open import Foundations.Prim.Type
open import Foundations.Sigma.Base       public
open import Foundations.Sigma.Properties public

open import Meta.Show

private variable
  ℓ : Level
  A B : Type ℓ

instance
  show-sigma : ⦃ _ : Show A ⦄ → ⦃ _ : Show B ⦄ → Show (A × B)
  show-sigma .shows-prec n (x , y) =
    "(" ++ₛ shows-prec n x ++ₛ " , " ++ₛ shows-prec n y ++ₛ ")"

private
  module _ where
    open import Data.Nat.Instances.Show

    _ : show (1 , 0) ＝ "(1 , 0)"
    _ = refl

    _ : show (1 , ((2 , 3) , (4 , 5))) ＝ "(1 , ((2 , 3) , (4 , 5)))"
    _ = refl
