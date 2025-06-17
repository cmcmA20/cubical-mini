{-# OPTIONS --safe #-}
module Data.String.Operations where

open import Foundations.Base
open import Meta.Effect

open import Data.String.Base
open import Data.Char
open import Data.List
open import Data.Nat
open import Data.Maybe

lengthₛ : String → ℕ
lengthₛ = length ∘ string→list

headₛ : String → Maybe Char
headₛ = map fst ∘ uncons

tailₛ : String → Maybe String
tailₛ = map snd ∘ uncons

concat-string : List String → String
concat-string []       = ""
concat-string (x ∷ xs) = x ++ₛ concat-string xs

words : List String → String
words x = concat-string $ intersperse " " x

lines : List String → String
lines x = concat-string $ intersperse "\n" x
