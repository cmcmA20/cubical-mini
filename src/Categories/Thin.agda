{-# OPTIONS --safe #-}
module Categories.Thin where

open import Categories.Prelude

is-thin : ∀ {o h} → Precategory o h → Type (o ⊔ h)
is-thin C = ∀ {x y} → is-prop (Precategory.Hom C x y)
