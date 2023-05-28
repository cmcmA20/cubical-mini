{-# OPTIONS --safe #-}
module Data.Sum.Base where

open import Foundations.Base

infixr 1 _⊎_
data _⊎_ {ℓ ℓ′} (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

private variable
  a b c d : Level
  A : Type a
  B : Type b
  C : Type c
  D : Type d

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

[]-η : (x : A ⊎ B) → [ inl , inr ]ᵤ x ＝ x
[]-η (inl x) = refl
[]-η (inr x) = refl

map : (A → C) → (B → D) → A ⊎ B → C ⊎ D
map f g (inl a) = inl (f a)
map f g (inr b) = inr (g b)

map-l : (A → C) → A ⊎ B → C ⊎ B
map-l f = map f id

map-r : (B → C) → A ⊎ B → A ⊎ C
map-r f = map id f
