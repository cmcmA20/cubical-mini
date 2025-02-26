{-# OPTIONS --safe #-}
module Foundations.Cat.Displayed.Reflexivity where

open import Foundations.Prim.Type

open import Foundations.Cat.Reflexivity

private variable ℓx : Level

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Refl Ob Hom ⦄
  {ob-lvlᴰ : Level → Level }
  {hom-lvlᴰ : Level → Level → Level }
  (Ob[_] : {ℓ : Level} → Ob ℓ → Type (ob-lvlᴰ ℓ))
  (Hom[_] : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} → Hom x y → Ob[ x ] → Ob[ y ] → Type (hom-lvlᴰ ℓx ℓy))
  where

  record Reflᴰ : Typeω where
    no-eta-equality
    field reflᴰ : {x : Ob ℓx} {x′ : Ob[ x ]} → Hom[ refl ] x′ x′

open Reflᴰ ⦃ ... ⦄ public

{-# DISPLAY Reflᴰ.reflᴰ _ = reflᴰ #-}
