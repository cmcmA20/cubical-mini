{-# OPTIONS --safe #-}
module Foundations.Notation.Whiskering.Outer where

open import Foundations.Prim.Type

open import Foundations.Notation.Composition

-- aka right whiskering
--        f                            f ∙ k
--   A ---|--> C                    A ---|--> X
--   |         ∥   k                |         ∥
-- h |    α    ∥ ---> X           h |  α ▷ k  ∥ k
--   v         ∥                    v         ∥
--   B ---|--> C                    B ---|--> X
--        g                            g ∙ k


module _
  {ℓx ℓa ℓb ℓc ℓf ℓg ℓk ℓfk ℓgk ℓh ℓis ℓos : Level}
  {X : 𝒰 ℓx} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {C : 𝒰 ℓc}
  (F : A → C → 𝒰 ℓf) (G : B → C → 𝒰 ℓg) (H : A → B → 𝒰 ℓh)
  (K : C → X → 𝒰 ℓk)
  (F∙K : A → X → 𝒰 ℓfk) ⦃ _ : Comp F K F∙K ⦄
  (G∙K : B → X → 𝒰 ℓgk) ⦃ _ : Comp G K G∙K ⦄
  (a : A) (b : B) (c : C) (x : X)
  (IS : (h : H a b) (f : F   a c) (g : G   b c) → 𝒰 ℓis)
  (OS : (h : H a b) (f : F∙K a x) (g : G∙K b x) → 𝒰 ℓos)
  where

  record Whisker-o : 𝒰 (ℓx ⊔ ℓa ⊔ ℓb ⊔ ℓc ⊔ ℓf ⊔ ℓg ⊔ ℓh ⊔ ℓk ⊔ ℓis ⊔ ℓos) where
    no-eta-equality
    infixr 24 _▷_
    field
      _▷_ : {f : F a c} {g : G b c} ⦃ h : H a b ⦄ → IS h f g
          → (k : K c x)
          → OS h (f ∙ k) (g ∙ k)

open Whisker-o ⦃ ... ⦄ public
{-# DISPLAY Whisker-o._▷_ _ a b = a ▷ b #-}
