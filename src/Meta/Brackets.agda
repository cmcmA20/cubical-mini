{-# OPTIONS --safe #-}
module Meta.Brackets where

open import Foundations.Prelude

record ⟦⟧-notation {ℓ} (A : Type ℓ) : Typeω where
  constructor brackets
  field
    {lvl} : Level
    Sem   : Type lvl
    ⟦_⟧   : A → Sem

open ⟦⟧-notation ⦃...⦄ public
  using(⟦_⟧)
{-# DISPLAY ⟦⟧-notation.⟦_⟧ f x = ⟦ x ⟧ #-}
