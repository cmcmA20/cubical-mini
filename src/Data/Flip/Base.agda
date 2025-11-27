{-# OPTIONS --safe #-}
module Data.Flip.Base where

open import Foundations.Base

-- symmetric closure
data Flip {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) : A → A → 𝒰 (ℓᵃ ⊔ ℓ) where
  fwd : ∀ {x y} → R x y → Flip R x y
  bwd : ∀ {x y} → R y x → Flip R x y

private variable
  ℓ ℓ′ : Level
  A B : 𝒰 ℓ
  R S : A → A → 𝒰 ℓ′
  x x′ y y′ z : A

-- TODO eliminator
rec : (∀ {a b} → R a b → S a b)
    → (∀ {a b} → S a b → S b a)
    → Flip R x y → S x y
rec g s (fwd r) = g r
rec g s (bwd r) = s (g r)

flip-sng : R x y → Flip R x y
flip-sng = fwd

flip-sym : Flip R x y → Flip R y x
flip-sym (fwd r) = bwd r
flip-sym (bwd r) = fwd r

instance
  Sym-Flip : Sym (Flip R)
  Sym-Flip Dual.ᵒᵖ = flip-sym

flip-map : {f : A → B}
         → (∀ {a b} → R a b → S (f a) (f b))
         → Flip R x y → Flip S (f x) (f y)
flip-map g = rec (flip-sng ∘ g) flip-sym

flip-concat : Flip (Flip R) x y → Flip R x y
flip-concat = rec id flip-sym
