{-# OPTIONS --safe #-}
module Data.Sum.Exclusive.Base where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Empty.Base
import Data.Reflects.Base as Reflects
open Reflects using (ofʸ; ofⁿ)

data _⊻ₜ_ {ℓ ℓ′} (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  inxl : A → ¬ B → A ⊻ₜ B
  inxr : B → ¬ A → A ⊻ₜ B

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  D : Type ℓᵈ

instance
  ⊻-Type : ⊻-notation (Type ℓᵃ) (Type ℓᵇ) (Type (ℓᵃ ⊔ ℓᵇ))
  ⊻-Type .⊻-notation.Constraint _ _ = ⊤ₜ
  ⊻-Type ._⊻_ A B = A ⊻ₜ B

[_,_]ₓ : (A → ¬ B → C) → (B → ¬ A → C) → (A ⊻ B) → C
[ f , _ ]ₓ (inxl a ¬b) = f a ¬b
[ _ , g ]ₓ (inxr b ¬a) = g b ¬a

[]ₓ-unique
  : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
    {f : A → ¬ B → C} {g : B → ¬ A → C}
    {h : A ⊻ B → C}
  → f ＝ curry² (h ∘ inxl $²_)
  → g ＝ curry² (h ∘ inxr $²_)
  → [ f , g ]ₓ ＝ h
[]ₓ-unique p q = fun-ext λ where
  (inxl a ¬b) i → p i a ¬b
  (inxr b ¬a) i → q i b ¬a

[]ₓ-η : (x : A ⊻ B) → [ inxl , inxr ]ₓ x ＝ x
[]ₓ-η (inxl _ _) = refl
[]ₓ-η (inxr _ _) = refl

qmap : (A → C) → (¬ A → ¬ C) → (B → D) → (¬ B → ¬ D) → A ⊻ B → C ⊻ D
qmap f f̂ g ĝ (inxl a ¬b) = inxl (f a) (ĝ ¬b)
qmap f f̂ g ĝ (inxr b ¬a) = inxr (g b) (f̂ ¬a)

dmap-l : (A → C) → (¬ A → ¬ C) → A ⊻ B → C ⊻ B
dmap-l f f̂ = qmap f f̂ id id

dmap-r : (B → C) → (¬ B → ¬ C) → A ⊻ B → A ⊻ C
dmap-r = qmap id id

instance
  ⊻-So : {x y : Bool} → ⊻-notation (So x) (So (not y)) (So (x xor y))
  ⊻-So .⊻-notation.Constraint _ _ = ⊤ₜ
  ⊻-So {x = true} {y = false} ._⊻_ _ _ = oh -- biased

  Reflects-⊻
    : ∀{ℓ ℓ′} {P : Type ℓ} {Q : Type ℓ′} {x y : Bool}
    → ⦃ rp : Reflects P x ⦄ ⦃ rq : Reflects Q y ⦄ → Reflects (P ⊻ Q) (x xor y)
  Reflects-⊻ {x = false} {y = false} ⦃ ofⁿ ¬p ⦄ ⦃ ofⁿ ¬q ⦄ = ofⁿ [ (λ z _ → ¬p z) , (λ z _ → ¬q z) ]ₓ
  Reflects-⊻ {x = false} {y = true}  ⦃ ofⁿ ¬p ⦄ ⦃ ofʸ  q ⦄ = ofʸ (inxr q ¬p)
  Reflects-⊻ {x = true}  {y = false} ⦃ ofʸ  p ⦄ ⦃ ofⁿ ¬q ⦄ = ofʸ (inxl p ¬q)
  Reflects-⊻ {x = true}  {y = true}  ⦃ ofʸ  p ⦄ ⦃ ofʸ  q ⦄ = ofⁿ [ (λ _ → _$ q) , (λ _ → _$ p) ]ₓ

reflects-xor : {x y : Bool} → Reflects (⌞ x ⌟ ⊻ ⌞ y ⌟) (x xor y)
reflects-xor = auto

is-inxl? is-inxr? : A ⊻ B → Bool
is-inxl? (inxl _ _) = true
is-inxl? (inxr _ _) = false
is-inxr? = not ∘ is-inxl?
