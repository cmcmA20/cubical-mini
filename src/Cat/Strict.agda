{-# OPTIONS --safe #-}
module Cat.Strict where

open import Cat.Prelude

is-strict : ∀ {o h} → Precategory o h → Type o
is-strict C = is-set ⌞ C ⌟
