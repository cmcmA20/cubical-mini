{-# OPTIONS --safe #-}
module Data.Bool.Properties where

open import Foundations.Base

open import Structures.Negation

open import Data.Bool.Base public

true≠false : ¬ true ＝ false
true≠false p = subst discrim p tt where
  discrim : Bool → Type
  discrim true  = ⊤
  discrim false = ⊥

-- module test where
--   open import Data.Id
--   Bool-is-setⁱ : is-setⁱ Bool
--   Bool-is-setⁱ false false reflⁱ reflⁱ = reflⁱ
--   Bool-is-setⁱ true  true  reflⁱ reflⁱ = reflⁱ

--   Bool-is-set′ : is-set Bool
--   Bool-is-set′ = is-setⁱ→is-set Bool-is-setⁱ
