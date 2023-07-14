{-# OPTIONS --safe #-}
module Data.Nat.Properties where

open import Foundations.Base

open import Data.Dec.Base
open import Data.Id

open import Data.Nat.Base public

+-zeror : (x : ℕ) → x + 0 ＝ x
+-zeror zero    = refl
+-zeror (suc x) = ap suc (+-zeror x)

+-sucr : (x y : ℕ) → x + suc y ＝ suc (x + y)
+-sucr zero y    = refl
+-sucr (suc x) y = ap suc (+-sucr x y)

+-comm : (x y : ℕ) → x + y ＝ y + x
+-comm zero y = sym (+-zeror y)
+-comm (suc x) y = ap suc (+-comm x y) ∙ sym (+-sucr y x)

-- TODO
