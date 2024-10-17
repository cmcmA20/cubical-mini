{-# OPTIONS --safe #-}
module Foundations.Notation.Whiskering.Inner where

open import Foundations.Prim.Type

open import Foundations.Notation.Composition

-- aka left whiskering
--             f                       h ∙ f
--        A ---|--> B               X ---|--> B
--    h   ∥         |               ∥         |
-- X ---> ∥    α    | k             ∥  h ◁ α  | k
--        ∥         v               ∥         v
--        A ---|--> C               X ---|--> C
--             g                       h ∙ g


module _
  {ℓx ℓa ℓb ℓc ℓf ℓg ℓh ℓhf ℓhg ℓk ℓis ℓos : Level}
  {X : 𝒰 ℓx} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {C : 𝒰 ℓc}
  (H : X → A → 𝒰 ℓh)
  (F : A → B → 𝒰 ℓf) (G : A → C → 𝒰 ℓg) (K : B → C → 𝒰 ℓk)
  (H∙F : X → B → 𝒰 ℓhf) ⦃ _ : Comp H F H∙F ⦄
  (H∙G : X → C → 𝒰 ℓhg) ⦃ _ : Comp H G H∙G ⦄
  (x : X) (a : A) (b : B) (c : C)
  (IS : (k : K b c) (f : F   a b) (g : G   a c) → 𝒰 ℓis)
  (OS : (k : K b c) (f : H∙F x b) (g : H∙G x c) → 𝒰 ℓos)
  where

  record Whisker-i : 𝒰 (ℓx ⊔ ℓa ⊔ ℓb ⊔ ℓc ⊔ ℓf ⊔ ℓg ⊔ ℓh ⊔ ℓk ⊔ ℓis ⊔ ℓos) where
    no-eta-equality
    infixr 24 _◁_
    field
      _◁_ : (h : H x a)
          → {f : F a b} {g : G a c} ⦃ k : K b c ⦄ → IS k f g
          → OS k (h ∙ f) (h ∙ g)

open Whisker-i ⦃ ... ⦄ public
{-# DISPLAY Whisker-i._◁_ _ a b = a ◁ b #-}
