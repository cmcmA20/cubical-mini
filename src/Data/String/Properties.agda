{-# OPTIONS --safe #-}
module Data.String.Properties where

open import Data.String.Base public

open import Agda.Builtin.String.Properties public
  using ()
  renaming
    ( primStringToListInjective   to string-to-list-inj
      -- string-to-list-inj : ∀ a b → primStringToList a ≡ primStringToList b → a ≡ b
    ; primStringFromListInjective to string-from-list-inj
      -- string-from-list-inj : ∀ a b → primStringFromList a ≡ primStringFromList b → a ≡ b
    )
