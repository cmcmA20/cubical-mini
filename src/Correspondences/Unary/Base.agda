{-# OPTIONS --safe #-}
module Correspondences.Unary.Base where

open import Foundations.Base

open import Meta.Search.HLevel

open import Structures.n-Type

open import Correspondences.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ

_⇒_ : Pred ℓ′ A → Pred ℓ″ A → Pred _ A
P ⇒ Q = λ x → P x → Q x

_⇒₁_ : Pred₁ ℓ′ A → Pred₁ ℓ″ A → Pred₁ _ A
P ⇒₁ Q = λ x → el! (⌞ P x ⌟ → ⌞ Q x ⌟)

infix 10 Universal Universal₁ IUniversal IUniversal₁

Universal : Pred ℓ′ A → _
Universal {A} P = Π[ a ꞉ A ] P a

syntax Universal P = Π[ P ]

Universal₁ : Pred₁ ℓ′ A → _
Universal₁ {A} P = Π[ a ꞉ A ] ⌞ P a ⌟

syntax Universal₁ P = Π[ P ]₁

IUniversal : Pred ℓ′ A → _
IUniversal P = ∀{a} → P a

syntax IUniversal P = ∀[ P ]

IUniversal₁ : Pred₁ ℓ′ A → _
IUniversal₁ P = ∀{a} → ⌞ P a ⌟

syntax IUniversal₁ P = ∀[ P ]₁
