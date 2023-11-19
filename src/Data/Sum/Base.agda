{-# OPTIONS --safe #-}
module Data.Sum.Base where

open import Foundations.Base

open import Meta.Variadic

infixr 7 _⊎_
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

[]ᵤ-η : (x : A ⊎ B) → [ inl , inr ]ᵤ x ＝ x
[]ᵤ-η (inl x) = refl
[]ᵤ-η (inr x) = refl

map : (A → C) → (B → D) → A ⊎ B → C ⊎ D
map f g (inl a) = inl (f a)
map f g (inr b) = inr (g b)

map-l : (A → C) → A ⊎ B → C ⊎ B
map-l f = map f id

map-r : (B → C) → A ⊎ B → A ⊎ C
map-r f = map id f


Sumⁿ : Variadic²
Sumⁿ = Lift-op²⃑ⁿ _⊎_

infixr 7 _⊎̇_
macro _⊎̇_ = binop-macro (quote Sumⁿ)
