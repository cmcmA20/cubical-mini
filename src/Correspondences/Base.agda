{-# OPTIONS --safe #-}
module Correspondences.Base where

open import Foundations.Base

open import Meta.Search.HLevel

open import Structures.n-Type

open import Data.Nat.Base
open import Data.Product.Base

Corr
  : (arity : ℕ) (ℓ′ : Level)
    {ℓ : Level} (A : Type ℓ)
  → Type (Levelₓ ℓ (ℓsuc ℓ′) arity)
Corr arity ℓ′ A = functionₓ arity A (Type ℓ′)

Pred : (ℓ′ : Level) {ℓ : Level} (A : Type ℓ) → Type (ℓ ⊔ ℓsuc ℓ′)
Pred = Corr 1


n-Corr
  : (arity : ℕ) (n : HLevel) (ℓ′ : Level)
    {ℓ : Level} (A : Type ℓ)
  → Type (Levelₓ ℓ (ℓsuc ℓ′) arity)
n-Corr arity n ℓ′ A = functionₓ arity A (n-Type ℓ′ n)

n-Corr⁰ = n-Corr 0
n-Corr¹ = n-Corr 1
n-Corr² = n-Corr 2
n-Corr³ = n-Corr 3

⌞_⌟ₚ : {ℓ ℓ′ : Level} {arity : ℕ} {n : HLevel} {A : Type ℓ} → n-Corr arity n ℓ′ A → Corr arity ℓ′ A
⌞_⌟ₚ {arity = 0} C = ⌞ C ⌟
⌞_⌟ₚ {arity = suc _} C a = ⌞ C a ⌟ₚ

Rel
  : (arity : ℕ) (ℓ′ : Level)
    {ℓ : Level} (A : Type ℓ)
  → Type (Levelₓ ℓ (ℓsuc ℓ′) arity)
Rel arity = n-Corr arity 1

Rel⁰ = Rel 0
Rel¹ = Rel 1
Rel² = Rel 2
Rel³ = Rel 3

n-Pred : (n : HLevel) (ℓ′ : Level) {ℓ : Level} (A : Type ℓ) → Type (ℓ ⊔ ℓsuc ℓ′)
n-Pred = n-Corr 1

Pred₀ = n-Pred 0
Pred₁ = n-Pred 1
Pred₂ = n-Pred 2


-- Unary

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  n : HLevel

_⇒_ : Pred ℓ′ A → Pred ℓ″ A → Pred _ A
P ⇒ Q = λ x → P x → Q x

_⇒ₙ_ : n-Pred n ℓ′ A → n-Pred n ℓ″ A → n-Pred n _ A
P ⇒ₙ Q = λ x → el! (⌞ P x ⌟ → ⌞ Q x ⌟)

infix 10 Universal Universalₙ IUniversal IUniversalₙ

Universal : Pred ℓ′ A → _
Universal {A} P = Π[ a ꞉ A ] P a

syntax Universal P = Π[ P ]

Universalₙ : n-Pred n ℓ′ A → _
Universalₙ {A} P = Universal (⌞_⌟ ∘ P)

syntax Universalₙ P = Π[ P ]ₙ

IUniversal : Pred ℓ′ A → _
IUniversal P = ∀{a} → P a

syntax IUniversal P = ∀[ P ]

IUniversalₙ : n-Pred n ℓ′ A → _
IUniversalₙ P = ∀{a} → ⌞ P a ⌟

syntax IUniversalₙ P = ∀[ P ]ₙ
