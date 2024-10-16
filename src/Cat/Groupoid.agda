{-# OPTIONS --safe #-}
module Cat.Groupoid where

open import Cat.Prelude
import Cat.Morphism

is-pregroupoid : ∀ {o h} → Precategory o h → Type (o ⊔ h)
is-pregroupoid C = {x y : Ob} (f : x ⇒ y) → quasi-inverse f where
  open Cat.Morphism C
