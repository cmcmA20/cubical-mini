{-# OPTIONS --safe #-}
module Foundations.Cat.Underlying where

open import Foundations.Prim.Type

private variable ℓ : Level

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  where

  record Underlying : Typeω where
    no-eta-equality
    field
      ℓ-und : Level → Level
      ⌞_⌟   : Ob ℓ → Type (ℓ-und ℓ)

open Underlying ⦃ ... ⦄ public
{-# DISPLAY Underlying.⌞_⌟ _ x = ⌞ x ⌟ #-}
