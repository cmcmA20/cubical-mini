{-# OPTIONS --safe #-}
module Categories.Groupoid where

open import Categories.Prelude
import Categories.Morphism

is-pregroupoid : ∀ {o h} → Precategory o h → Type (o ⊔ h)
is-pregroupoid C = ∀ {x y} (f : Hom x y) → is-invertible f where
  open Categories.Morphism C
