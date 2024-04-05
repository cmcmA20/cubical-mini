{-# OPTIONS --safe #-}
module Data.String.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Char.Base
open import Data.Id.Inductive
open import Data.List.Base

open import Data.String.Base public

open import Agda.Builtin.String.Properties public
  using ()
  renaming
    ( primStringToListInjective   to string→list-injⁱ
      -- string-to-list-inj : ∀ a b → primStringToList a ≡ primStringToList b → a ≡ b
    ; primStringFromListInjective to list→string-injⁱ
      -- string-from-list-inj : ∀ a b → primStringFromList a ≡ primStringFromList b → a ≡ b
    )

string→list-inj : {s₁ s₂ : String} → string→list s₁ ＝ string→list s₂ → s₁ ＝ s₂
string→list-inj = Id≃path.to ∘ string→list-injⁱ _ _ ∘ Id≃path.from

list→string-inj : {xs ys : List Char} → list→string xs ＝ list→string ys → xs ＝ ys
list→string-inj = Id≃path.to ∘ list→string-injⁱ _ _ ∘ Id≃path.from
