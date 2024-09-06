{-# OPTIONS --safe #-}
module Cat.Thin where

open import Cat.Prelude

is-thin : ∀ {o h} → Precategory o h → Type (o ⊔ h)
is-thin C = ∀ {x y} → is-prop (Precategory.Hom C x y)
