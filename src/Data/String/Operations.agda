{-# OPTIONS --safe #-}
module Data.String.Operations where

open import Foundations.Base
open import Meta.Effect

open import Data.String.Base
open import Data.Char
open import Data.List
open import Data.Nat
open import Data.Maybe

char→string : Char → String
char→string c = list→string $ c ∷ []

lengthₛ : String → ℕ
lengthₛ = length ∘ string→list

headₛ : String → Maybe Char
headₛ = map fst ∘ uncons

tailₛ : String → Maybe String
tailₛ = map snd ∘ uncons

replicateₛ : ℕ → Char → String
replicateₛ n = list→string ∘ replicate n

concat-string : List String → String
concat-string []       = ""
concat-string (x ∷ xs) = x ++ₛ concat-string xs

words : List String → String
words x = concat-string $ intersperse " " x

lines : List String → String
lines x = concat-string $ intersperse "\n" x

substring : ℕ → ℕ → String → String
substring start end str =
  list→string $
  take (end ∸ start) $
  drop start $
  string→list str
