{-# OPTIONS --safe #-}
module Data.Flip.Path where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel
open import Data.Sum.Base
open import Data.Sum.Path
open import Data.Sum.Properties
open import Data.Flip.Base

private variable
  ℓ ℓ′ : Level
  A B : 𝒰 ℓ
  R : A → A → 𝒰 ℓ′
  x x′ y y′ z : A

Flip≃⊎ : Flip R x y ≃ (R x y ⊎ R y x)
Flip≃⊎ {R} =
  ≅→≃ $
  make-iso (rec inl (⊎-comm $_))
           [ fwd , bwd ]ᵤ $
  make-inverses
    (fun-ext re)
    (fun-ext se)
  where
  re : (q : R x y ⊎ R y x) → rec {R = R} inl (⊎-comm $_) ([ fwd , bwd ]ᵤ q) ＝ q
  re (inl x) = refl
  re (inr x) = refl
  se : (q : Flip R x y) → [ fwd , bwd ]ᵤ (rec {R = R} inl (⊎-comm $_) q) ＝ q
  se (fwd x) = refl
  se (bwd x) = refl

Flip-is-of-hlevel : (n : HLevel)
                  → (∀ {x y} → is-of-hlevel (2 + n) (R x y))
                  → ∀ {x y} → is-of-hlevel (2 + n) (Flip R x y)
Flip-is-of-hlevel n hl {x} {y} =
  ≃→is-of-hlevel (2 + n) Flip≃⊎ (⊎-is-of-hlevel n (hl {x} {y}) (hl {y} {x}))
