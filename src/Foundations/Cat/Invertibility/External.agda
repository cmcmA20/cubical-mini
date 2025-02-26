{-# OPTIONS --safe #-}
module Foundations.Cat.Invertibility.External where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition
open import Foundations.Cat.Diagram.Coproduct.Indexed

open import Foundations.HLevel.Base

private variable ℓx ℓy : Level

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄ (ℓ : Level) {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y)
  where

  is-inv-o : Type (ob-lvl ℓ l⊔ hom-lvl ℓ ℓx l⊔ hom-lvl ℓ ℓy)
  is-inv-o = (z : Ob ℓ) (h : Hom z y) → is-contr (Σₜ (Hom z x) λ g → g ∙ f ＝ h)

  is-inv-i : Type (ob-lvl ℓ l⊔ hom-lvl ℓx ℓ l⊔ hom-lvl ℓy ℓ)
  is-inv-i = (z : Ob ℓ) (h : Hom x z) → is-contr (Σₜ (Hom y z) λ g → f ∙ g ＝ h)
