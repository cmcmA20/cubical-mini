{-# OPTIONS --safe #-}
module Foundations.Cat.Associativity where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition

private variable ℓ ℓw ℓx ℓy ℓz : Level

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  ⦃ _ : Comp Ob Hom ⦄
  where

  record Assoc : Typeω where
    no-eta-equality
    field assoc : {w : Ob ℓw} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
                  (f : Hom w x) (g : Hom x y) (h : Hom y z)
                → f ∙ (g ∙ h) ＝ (f ∙ g) ∙ h

open Assoc ⦃ ... ⦄ public

{-# DISPLAY Assoc.assoc _ f g h = assoc f g h #-}
