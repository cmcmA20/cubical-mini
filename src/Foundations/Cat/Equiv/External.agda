{-# OPTIONS --safe #-}
module Foundations.Cat.Equiv.External where

open import Foundations.Prim.Type

open import Foundations.Cat.Composition
open import Foundations.Cat.Diagram.Product.Binary
open import Foundations.Cat.Invertibility.External

open import Foundations.HLevel.Base

private variable ℓx ℓy : Level

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄ (ℓ : Level) {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y)
  where

  is-equiv : Type (ob-lvl ℓ l⊔ hom-lvl ℓx ℓ l⊔ hom-lvl ℓy ℓ l⊔ hom-lvl ℓ ℓx l⊔ hom-lvl ℓ ℓy)
  is-equiv = is-inv-o ℓ f × is-inv-i ℓ f
