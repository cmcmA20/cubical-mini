{-# OPTIONS --safe --no-exact-split #-}
module Cat.Functor.Properties where

open import Cat.Prelude
open import Cat.Functor.Base

private variable
  oᶜ hᶜ oᵈ hᵈ : Level
  C : Precategory oᶜ hᶜ
  D : Precategory oᵈ hᵈ

is-full : C ⇒ D → Type _
is-full {C} {D} F =
    {x y : C.Ob} (g : F # x ⇒ F # y)
  → ∃[ f ꞉ x ⇒ y ] (F # f ＝ g)
    where
      module C = Precategory C
      module D = Precategory D

is-faithful : C ⇒ D → Type _
is-faithful {C} F = {x y : C.Ob} → Injective (Functor.F₁ F {x} {y})
  where module C = Precategory C

is-fully-faithful : C ⇒ D → Type _
is-fully-faithful {C} F = {x y : C.Ob} → is-equiv (Functor.F₁ F {x} {y})
  where module C = Precategory C
