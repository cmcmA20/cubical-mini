{-# OPTIONS --safe #-}
module Data.Sum.Base where

open import Foundations.Base

infixr 7 _⊎ₜ_
data _⊎ₜ_ {ℓ ℓ′} (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  inl : A → A ⊎ₜ B
  inr : B → A ⊎ₜ B

private variable
  a b c d : Level
  A : Type a
  B : Type b
  C : Type c
  D : Type d

instance
  ⊎-Type : ⊎-notation (Type a) (Type b) (Type (a ⊔ b))
  ⊎-Type ._⊎_ = _⊎ₜ_

  Union-pow
    : {A : Type a} {B : Type b} ⦃ ua : Underlying A ⦄ ⦃ ub : Underlying B ⦄
      {P : Type c} {X : Type d}
      ⦃ _ : ⊎-notation (Type (ua .ℓ-underlying)) (Type (ub .ℓ-underlying)) P ⦄
    → Union (X → A) (X → B) (X → P)
  Union-pow ._∪_ S T x = ⌞ S x ⌟ ⊎ ⌞ T x ⌟
  {-# OVERLAPPABLE Union-pow #-}

[_,_]ᵤ : (A → C) → (B → C) → (A ⊎ B) → C
[ f , _ ]ᵤ (inl x) = f x
[ _ , g ]ᵤ (inr x) = g x

[]ᵤ-unique
  : ∀ {f : A → C} {g : B → C} {h}
  → f ＝ h ∘ inl
  → g ＝ h ∘ inr
  → [ f , g ]ᵤ ＝ h
[]ᵤ-unique p q = fun-ext λ where
  (inl x) i → p i x
  (inr x) i → q i x

[]ᵤ-η : (x : A ⊎ B) → [ inl , inr ]ᵤ x ＝ x
[]ᵤ-η (inl x) = refl
[]ᵤ-η (inr x) = refl

dmap : (A → C) → (B → D) → A ⊎ B → C ⊎ D
dmap f g (inl a) = inl (f a)
dmap f g (inr b) = inr (g b)

map-l : (A → C) → A ⊎ B → C ⊎ B
map-l f = dmap f id

map-r : (B → C) → A ⊎ B → A ⊎ C
map-r f = dmap id f
