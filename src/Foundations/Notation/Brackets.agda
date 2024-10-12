{-# OPTIONS --safe #-}
module Foundations.Notation.Brackets where

open import Foundations.Prim.Type

record ⟦⟧-notation {ℓ} (A : Type ℓ) : Typeω where
  constructor brackets
  field
    {lvl} : Level
    Sem   : Type lvl
    ⟦_⟧   : A → Sem

open ⟦⟧-notation ⦃...⦄ public
  using(⟦_⟧)
{-# DISPLAY ⟦⟧-notation.⟦_⟧ _ x = ⟦ x ⟧ #-}
