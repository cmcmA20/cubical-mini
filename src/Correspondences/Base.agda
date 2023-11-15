{-# OPTIONS --safe #-}
module Correspondences.Base where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel

open import Structures.n-Type

open import Truncation.Propositional.Base

open import Data.Product.Base public

-- Heterogeneous correspondences
Corr
  : (arity : ℕ) (ℓ : Level)
    {ls : Levels arity} (As : Types arity ls)
  → Type (ℓsuc ℓ ⊔ ℓsup arity ls)
Corr arity ℓ As = Arrows arity As (Type ℓ)

Corr⁰ = Corr 0
Corr¹ = Corr 1
Corr² = Corr 2
Corr³ = Corr 3
Corr⁴ = Corr 4
Corr⁵ = Corr 5

-- FIXME a bit opinionated?
-- Unary correspondence is called a predicate
Pred : (ℓ : Level) {ℓᵃ : Level} (A : Type ℓᵃ) → Type (ℓᵃ ⊔ ℓsuc ℓ)
Pred = Corr¹


-- n-truncated correspondence
n-Corr
  : (arity : ℕ) (n : HLevel) (ℓ : Level)
    {ls : Levels arity} (As : Types arity ls)
  → Type (ℓsuc ℓ ⊔ ℓsup arity ls)
n-Corr arity n ℓ As = Arrows arity As (n-Type ℓ n)

n-Corr⁰ = n-Corr 0
n-Corr¹ = n-Corr 1
n-Corr² = n-Corr 2
n-Corr³ = n-Corr 3
n-Corr⁴ = n-Corr 4
n-Corr⁵ = n-Corr 5

Carrierⁿ : {ℓ : Level} {arity : ℕ} {n : HLevel} {ls : Levels arity} {As : Types _ ls} → n-Corr arity n ℓ As → Corr arity ℓ As
Carrierⁿ {arity = 0}           C   = ⌞ C ⌟
Carrierⁿ {arity = 1}           C a = ⌞ C a ⌟
Carrierⁿ {arity = suc (suc _)} C a = Carrierⁿ (C a)


-- Propositionally valued correspondence is called a relation
Rel
  : (arity : ℕ) (ℓ : Level)
    {ls : Levels arity} (As : Types arity ls)
  → Type (ℓsuc ℓ ⊔ ℓsup arity ls)
Rel arity = n-Corr arity 1

Rel⁰ = Rel 0
Rel¹ = Rel 1
Rel² = Rel 2
Rel³ = Rel 3
Rel⁴ = Rel 4
Rel⁵ = Rel 5

n-Pred : (n : HLevel) (ℓ′ : Level) {ℓ : Level} (A : Type ℓ) → Type (ℓ ⊔ ℓsuc ℓ′)
n-Pred = n-Corr¹

Pred₀ = n-Pred 0
Pred₁ = n-Pred 1
Pred₂ = n-Pred 2
Pred₃ = n-Pred 3
Pred₄ = n-Pred 4
Pred₅ = n-Pred 5


private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  n : HLevel
  arity : ℕ

Universalⁿ : {ls : Levels arity} {As : Types arity ls} → Corr arity ℓ As → Type (ℓ ⊔ ℓsup arity ls)
Universalⁿ {0}                         P = P
Universalⁿ {1}           {As = A}      P = Π[ a ꞉ A ] P a
Universalⁿ {suc (suc _)} {As = A , As} P = Π[ a ꞉ A ] Universalⁿ (P a)

IUniversalⁿ : {ls : Levels arity} {As : Types arity ls} → Corr arity ℓ As → Type (ℓ ⊔ ℓsup arity ls)
IUniversalⁿ {0}                         P = P
IUniversalⁿ {1}           {As = A}      P = ∀{a} → P a
IUniversalⁿ {suc (suc _)} {As = A , As} P = ∀{a} → IUniversalⁿ (P a)

Existentialⁿ : {ls : Levels arity} {As : Types arity ls} → Corr arity ℓ As → Type (ℓ ⊔ ℓsup arity ls)
Existentialⁿ {0}                         P = P
Existentialⁿ {1}           {As = A}      P = Σ[ a ꞉ A ] P a
Existentialⁿ {suc (suc _)} {As = A , As} P = Σ[ a ꞉ A ] Existentialⁿ (P a)

Existential₁ⁿ : {ls : Levels arity} {As : Types arity ls} → Corr arity ℓ As → Type (ℓ ⊔ ℓsup arity ls)
Existential₁ⁿ {0}                         P = ∥ P ∥₁
Existential₁ⁿ {1}           {As = A}      P = ∃[ a ꞉ A ] P a
Existential₁ⁿ {suc (suc _)} {As = A , As} P = ∥ Σ[ a ꞉ A ] Existentialⁿ (P a) ∥₁

Implⁿ : {ls : Levels arity} {As : Types arity ls} → Corr arity ℓ As → Corr arity ℓ′ As → Corr arity (ℓ ⊔ ℓ′) As
Implⁿ {0}           P Q = P → Q
Implⁿ {1}           P Q = λ x → P x → Q x
Implⁿ {suc (suc _)} P Q = λ x → Implⁿ (P x) (Q x)


-- Binary homogeneous correspondences

Reflexive : Corr² ℓ (A , A) → Type _
Reflexive _~_ = ∀ {x} → x ~ x

Symmetric : Corr² ℓ (A , A) → Type _
Symmetric _~_ = ∀ {x y} → (x ~ y) → (y ~ x)

Transitive : Corr² ℓ (A , A) → Type _
Transitive _~_ = ∀ {x y z} → (x ~ y) → (y ~ z) → (x ~ z)

record Equivalence (_~_ : Corr² ℓ (A , A)) : Type (level-of-type A ⊔ ℓ) where
  field
    reflᶜ : Reflexive _~_
    symᶜ  : Symmetric _~_
    _∙ᶜ_  : Transitive _~_

record is-congruence (_~_ : Corr² ℓ (A , A)) : Type (level-of-type A ⊔ ℓ) where
  field
    equivalenceᶜ : Equivalence _~_
    has-propᶜ : ∀ {x y} → is-prop (x ~ y)

  instance
    H-Level-~ : ∀ {x y} → H-Level (suc n) (x ~ y)
    H-Level-~ = hlevel-prop-instance has-propᶜ
  open Equivalence equivalenceᶜ public
