{-# OPTIONS --safe #-}
module Data.String.Internal where

open import Agda.Builtin.String public
  using( String )
  renaming
    ( primStringUncons   to uncons
    ; primStringToList   to to-list
    ; primStringFromList to from-list
    ; primShowString     to show-str
    ; primShowNat        to show-ℕ )

open import Agda.Builtin.String.Properties public
  using ()
  renaming
    ( primStringToListInjective   to string-to-list-injective
      -- string-to-list-injective : ∀ a b → primStringToList a ≡ primStringToList b → a ≡ b
    ; primStringFromListInjective to string-from-list-injective
      -- string-from-list-injective : ∀ a b → primStringFromList a ≡ primStringFromList b → a ≡ b
    )
