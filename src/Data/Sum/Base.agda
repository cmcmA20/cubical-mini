{-# OPTIONS --safe #-}
module Data.Sum.Base where

open import Foundations.Base

open import Data.Bool.Base
  using (Bool; So; _or_; oh; true; false; not)
open import Data.Empty.Base
  using ()
import Data.Reflects.Base as Reflects
open Reflects using (ofʸ; ofⁿ)

infixr 7 _⊎ₜ_
data _⊎ₜ_ {ℓ ℓ′} (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  inl : A → A ⊎ₜ B
  inr : B → A ⊎ₜ B

private variable
  ℓ ℓ′ ℓ″ ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  D : Type ℓᵈ

instance
  ⊎-Type : ⊎-notation (Type ℓᵃ) (Type ℓᵇ) (Type (ℓᵃ ⊔ ℓᵇ))
  ⊎-Type .⊎-notation.Constraint _ _ = ⊤ₜ
  ⊎-Type ._⊎_ A B = A ⊎ₜ B

  Union-pow
    : ⦃ ua : Underlying A ⦄ ⦃ ub : Underlying B ⦄
      {X : Type ℓ′} {P : Type ℓ} ⦃ up : Underlying P ⦄
      ⦃ un : ⊎-notation {ℓ′ = ℓ″} (Type (ua .ℓ-underlying)) (Type (ub .ℓ-underlying)) P ⦄
      ⦃ _ : ∀ {x y} → un .⊎-notation.Constraint x y ⦄
    → Union (X → A) (X → B) (X → P)
  Union-pow ._∪_ S T x = ⌞ S x ⌟ ⊎ ⌞ T x ⌟
  {-# OVERLAPPABLE Union-pow #-}

elim : {C : A ⊎ B → Type ℓ′}
     → ((a : A) → C (inl a))
     → ((b : B) → C (inr b))
     → (d : A ⊎ B) → C d
elim l _ (inl a) = l a
elim _ r (inr b) = r b

[_,_]ᵤ : (A → C) → (B → C) → (A ⊎ B) → C
[_,_]ᵤ = elim

[]ᵤ-unique
  : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
    {f : A → C} {g : B → C} {h : A ⊎ B → C}
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

instance
  ⊎-Fun : {A : Type ℓᵃ} {B : Type ℓᵇ} {X : Type ℓ} {Y : Type ℓ′}
        → ⊎-notation (A → X) (B → Y) (A ⊎ B → X ⊎ Y)
  ⊎-Fun .⊎-notation.Constraint _ _ = ⊤ₜ
  ⊎-Fun ._⊎_ f g = dmap f g
  {-# INCOHERENT ⊎-Fun #-}

  ⊎-Funᵈ : {A : Type ℓᵃ} {B : Type ℓᵇ} {X : A → Type ℓ} {Y : B → Type ℓ}
        → ⊎-notation Π[ X ] Π[ Y ] Π[ [ X , Y ]ᵤ ]
  ⊎-Funᵈ .⊎-notation.Constraint _ _ = ⊤ₜ
  ⊎-Funᵈ ._⊎_ f g (inl a) = f a
  ⊎-Funᵈ ._⊎_ f g (inr b) = g b
  {-# INCOHERENT ⊎-Funᵈ #-}

  ⊎-So : {x y : Bool} → ⊎-notation (So x) (So y) (So (x or y))
  ⊎-So .⊎-notation.Constraint _ _ = ⊤ₜ
  ⊎-So {x = true} ._⊎_ _ _ = oh

  Reflects-⊎
    : {P : Type ℓ} {Q : Type ℓ′} {x y : Bool}
    → ⦃ rp : Reflects P x ⦄ ⦃ rq : Reflects Q y ⦄ → Reflects (P ⊎ Q) (x or y)
  Reflects-⊎ {x = false} {y} ⦃ ofⁿ ¬p ⦄ ⦃ ofⁿ ¬q ⦄ = ofⁿ [ ¬p , ¬q ]ᵤ
  Reflects-⊎ {x = false} {y} ⦃ ofⁿ ¬p ⦄ ⦃ ofʸ  q ⦄ = ofʸ (inr q)
  Reflects-⊎ {x = true}  {y} ⦃ ofʸ  p ⦄            = ofʸ (inl p)

reflects-or : {x y : Bool} → Reflects (⌞ x ⌟ ⊎ ⌞ y ⌟) (x or y)
reflects-or = auto

is-inl? is-inr? : A ⊎ B → Bool
is-inl? (inl _) = true
is-inl? (inr _) = false
is-inr? = not ∘ is-inl?
