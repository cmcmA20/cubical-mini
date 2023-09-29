{-# OPTIONS --safe #-}
module Correspondences.Powerset where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Structures.n-Type

open import Correspondences.Base public

open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Unit.Instances.HLevel

open import Truncation.Propositional.Base

private variable
  ℓ : Level
  X : Type ℓ
  x y : X

ℙ : Type ℓ → Type (ℓsuc ℓ)
ℙ X = X → Prop _

infix 5 _∈_
_∈_ : X → ℙ X → Type _
x ∈ A  = ⌞ A x ⌟

subst-∈ : (A : ℙ X) → x ＝ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

_⊆_ : ℙ X → ℙ X → Type _
A ⊆ B = ∀[ (_∈ A) ⇒ (_∈ B) ]

⊆-refl : (A : ℙ X) → A ⊆ A
⊆-refl _ = id

@0 ℙ-ext : {A B : ℙ X}
         → A ⊆ B → B ⊆ A → A ＝ B
ℙ-ext {A = A} {B = B} A⊆B B⊆A = fun-ext λ _ →
  n-ua (prop-extₑ! A⊆B B⊆A)

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
