{-# OPTIONS --safe #-}
module Correspondences.Base where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Structures.n-Type

open import Data.Nat.Base
open import Data.Product.Base public

Corr
  : (arity : ℕ) (ℓ′ : Level)
    {ℓ : Level} (A : Type ℓ)
  → Type (Levelₓ ℓ (ℓsuc ℓ′) arity)
Corr arity ℓ′ A = functionₓ arity A (Type ℓ′)

Corr⁰ = Corr 0
Corr¹ = Corr 1
Corr² = Corr 2
Corr³ = Corr 3

Pred : (ℓ′ : Level) {ℓ : Level} (A : Type ℓ) → Type (ℓ ⊔ ℓsuc ℓ′)
Pred = Corr¹


n-Corr
  : (arity : ℕ) (n : HLevel) (ℓ′ : Level)
    {ℓ : Level} (A : Type ℓ)
  → Type (Levelₓ ℓ (ℓsuc ℓ′) arity)
n-Corr arity n ℓ′ A = functionₓ arity A (n-Type ℓ′ n)

n-Corr⁰ = n-Corr 0
n-Corr¹ = n-Corr 1
n-Corr² = n-Corr 2
n-Corr³ = n-Corr 3

⌞_⌟ₙ : {ℓ ℓ′ : Level} {arity : ℕ} {n : HLevel} {A : Type ℓ} → n-Corr arity n ℓ′ A → Corr arity ℓ′ A
⌞_⌟ₙ {arity = 0} C = ⌞ C ⌟
⌞_⌟ₙ {arity = suc _} C a = ⌞ C a ⌟ₙ

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
n-Pred = n-Corr¹

Pred₀ = n-Pred 0
Pred₁ = n-Pred 1
Pred₂ = n-Pred 2
Pred₃ = n-Pred 3

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  n : HLevel
  arity : ℕ

infix 10 Universal IUniversal

Universal : Corr arity ℓ A → Type (level-of-type A ⊔ ℓ)
Universal {0} {A} P = Lift (level-of-type A) P
Universal {1} {A} P = Π[ a ꞉ A ] P a
Universal {suc (suc _)} {A} P = Π[ a ꞉ A ] Universal (P a)
{-# INLINE Universal #-}

syntax Universal P = Π[ P ]

IUniversal : Corr arity ℓ A → Type (level-of-type A ⊔ ℓ)
IUniversal {0} {A} P = Lift (level-of-type A) P
IUniversal {1} {A} P = ∀{a} → P a
IUniversal {suc (suc _)} {A} P = ∀{a} → IUniversal (P a)
{-# INLINE IUniversal #-}

syntax IUniversal P = ∀[ P ]

_⇒_ : Corr arity ℓ A → Corr arity ℓ′ A → Corr arity (ℓ ⊔ ℓ′) A
_⇒_ {0} P Q = P → Q
_⇒_ {suc _} P Q = λ x → P x ⇒ Q x

_⇒ₙ_ : n-Corr arity n ℓ A → n-Corr arity n ℓ′ A → n-Corr arity n (ℓ ⊔ ℓ′) A
_⇒ₙ_ {0} P Q = el! (⌞ P ⌟ → ⌞ Q ⌟)
_⇒ₙ_ {suc _} P Q = λ x → P x ⇒ₙ Q x

-- Unary
-- TODO nothing here


-- Binary

Reflexive : Corr 2 ℓ A → Type _
Reflexive _~_ = ∀ {x} → x ~ x

Symmetric : Corr 2 ℓ A → Type _
Symmetric _~_ = ∀ {x y} → (x ~ y) → (y ~ x)

Transitive : Corr 2 ℓ A → Type _
Transitive _~_ = ∀ {x y z} → (x ~ y) → (y ~ z) → (x ~ z)

record Equivalence (_~_ : Corr 2 ℓ A) : Type (level-of-type A ⊔ ℓ) where
  field
    reflᶜ : Reflexive _~_
    symᶜ  : Symmetric _~_
    _∙ᶜ_  : Transitive _~_

record is-congruence (_~_ : Corr 2 ℓ A) : Type (level-of-type A ⊔ ℓ) where
  field
    equivalenceᶜ : Equivalence _~_
    instance
      has-propᶜ    : ∀ {x y} → is-prop (x ~ y)
  open Equivalence equivalenceᶜ public
