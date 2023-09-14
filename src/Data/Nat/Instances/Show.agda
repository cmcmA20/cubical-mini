{-# OPTIONS --safe #-}
module Data.Nat.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Nat.Base
open import Data.String.Base

instance
  Show-ℕ : Show ℕ
  Show-ℕ .shows-prec _ = show-ℕ

_ : show (0 , 1) ＝ "0 , 1"
_ = refl

_ : show (1 , 2 , (3 , 4)) ＝ "1 , 2 , 3 , 4"
_ = refl

_ : show (1 , (2 , 3) , 4) ＝ "1 , (2 , 3) , 4"
_ = refl
