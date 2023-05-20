{-# OPTIONS --safe #-}
module Data.Sum.Base where

open import Foundations.Base

infixr 1 _⊎_
data _⊎_ {ℓ ℓ′} (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  inj-l : A → A ⊎ B
  inj-r : B → A ⊎ B

private variable
  a b c d : Level
  A : Type a
  B : Type b
  C : Type c
  D : Type d

[_,_]ᵤ : (A → C) → (B → C) → (A ⊎ B) → C
[ f , _ ]ᵤ (inj-l x) = f x
[ _ , g ]ᵤ (inj-r x) = g x

[]ᵤ-unique
  : ∀ {f : A → C} {g : B → C} {h}
  → f ＝ h ∘ inj-l
  → g ＝ h ∘ inj-r
  → [ f , g ]ᵤ ＝ h
[]ᵤ-unique p q = fun-ext λ where
  (inj-l x) i → p i x
  (inj-r x) i → q i x

[]-η : (x : A ⊎ B) → [ inj-l , inj-r ]ᵤ x ＝ x
[]-η (inj-l x) = refl
[]-η (inj-r x) = refl

map : (A → C) → (B → D) → A ⊎ B → C ⊎ D
map f g (inj-l a) = inj-l (f a)
map f g (inj-r b) = inj-r (g b)

map-l : (A → C) → A ⊎ B → C ⊎ B
map-l f = map f id

map-r : (B → C) → A ⊎ B → A ⊎ C
map-r f = map id f
