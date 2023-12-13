{-# OPTIONS --safe #-}
module Categories.Strict where

open import Categories.Prelude

is-strict : ∀ {o h} → Precategory o h → Type o
is-strict C = is-set (Precategory.Ob C)
