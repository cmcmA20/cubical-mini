{-# OPTIONS --safe #-}
module Data.String.Operations where

open import Data.String.Base
open import Foundations.Base

open import Data.List

concat-string : List String → String
concat-string []       = ""
concat-string (x ∷ xs) = x ++ₛ concat-string xs

words : List String → String
words x = concat-string $ intersperse " " x

lines : List String → String
lines x = concat-string $ intersperse "\n" x
