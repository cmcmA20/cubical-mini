{-# OPTIONS --safe #-}
module Foundations.Prim.Extension where

open import Foundations.Type
open import Foundations.Prim.Interval

open import Agda.Builtin.Cubical.Sub public
  using ( inS )
  renaming ( Sub to _[_↦_]
           ; primSubOut to outS )

private variable ℓ : Level

partial-pushout
  : (i j : I) {A : Partial (i ∨ j) (Type ℓ)}
    {ai : PartialP {a = ℓ} (i ∧ j) (λ { (j ∧ i = i1) → A 1=1 }) }
  → (.(z : IsOne i) → A (is1-left  i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → (.(z : IsOne j) → A (is1-right i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → PartialP (i ∨ j) A
partial-pushout i j u v = primPOr i j (λ z → outS (u z)) (λ z → outS (v z))
