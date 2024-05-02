{-# OPTIONS --safe #-}
module Combinatorics.Power.Base where

open import Meta.Prelude

open import Meta.Membership

open import Structures.n-Type

open import Data.Empty as ⊥
open import Data.Sum.Base
open import Data.Truncation.Propositional as ∥-∥₁
open import Data.Unit.Base

private variable
  ℓ : Level
  X : Type ℓ
  x y : X

ℙ : Type ℓ → Type (ℓsuc ℓ)
ℙ X = X → Prop _

private variable A B : ℙ X

subst-∈ : (A : ℙ X) {x y : X} → x ＝ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

⊆-refl : (A : ℙ X) → A ⊆ A
⊆-refl _ = refl

@0 ℙ-ext : A ⊆ B → B ⊆ A → A ＝ B
ℙ-ext A⊆B B⊆A = fun-ext λ _ → n-ua (prop-extₑ! A⊆B B⊆A)

single : ⦃ X-set : H-Level 2 X ⦄ → X → ℙ X
single x t = el! (x ＝ t)

infixr 22 _∩_
_∩_ : ℙ X → ℙ X → ℙ X
(A ∩ B) x = el! ((x ∈ A) × (x ∈ B))

infixr 21 _∪_
_∪_ : ℙ X → ℙ X → ℙ X
(A ∪ B) x = el! ((x ∈ A) ⊎₁ (x ∈ B))

⟙ : ℙ X
⟙ _ = el! (Lift _ ⊤)

⟘ : ℙ X
⟘ _ = el! (Lift _ ⊥)

⟘⊆ : ⟘ ⊆ A
⟘⊆ ()

@0 ⊆⟘→⟘ : A ⊆ ⟘ → A ＝ ⟘
⊆⟘→⟘ {A} p = ℙ-ext p (⟘⊆ {A = A})

⟙⊆ : A ⊆ ⟙
⟙⊆ = _
