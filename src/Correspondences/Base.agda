{-# OPTIONS --safe #-}
module Correspondences.Base where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Structures.n-Type

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

⌞_⌟ⁿ : {ℓ : Level} {arity : ℕ} {n : HLevel} {ls : Levels arity} {As : Types _ ls} → n-Corr arity n ℓ As → Corr arity ℓ As
⌞_⌟ⁿ {arity = 0}           C   = ⌞ C ⌟
⌞_⌟ⁿ {arity = 1}           C a = ⌞ C a ⌟
⌞_⌟ⁿ {arity = suc (suc _)} C a = ⌞ C a ⌟ⁿ

⌞_⌟¹ : {ℓ : Level} {n : HLevel} {ls : Levels 1} {As : Types _ ls} → n-Corr _ n ℓ As → _
⌞_⌟¹ = ⌞_⌟ⁿ {arity = 1}

⌞_⌟² : {ℓ : Level} {n : HLevel} {ls : Levels 2} {As : Types _ ls} → n-Corr _ n ℓ As → _
⌞_⌟² = ⌞_⌟ⁿ {arity = 2}

⌞_⌟³ : {ℓ : Level} {n : HLevel} {ls : Levels 3} {As : Types _ ls} → n-Corr _ n ℓ As → _
⌞_⌟³ = ⌞_⌟ⁿ {arity = 3}

⌞_⌟⁴ : {ℓ : Level} {n : HLevel} {ls : Levels 4} {As : Types _ ls} → n-Corr _ n ℓ As → _
⌞_⌟⁴ = ⌞_⌟ⁿ {arity = 4}

⌞_⌟⁵ : {ℓ : Level} {n : HLevel} {ls : Levels 5} {As : Types _ ls} → n-Corr _ n ℓ As → _
⌞_⌟⁵ = ⌞_⌟ⁿ {arity = 5}

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

infix 10 Universal Universal¹ Universal² Universal³ Universal⁴ Universal⁵

Universalⁿ : {ls : Levels arity} {As : Types arity ls} → Corr arity ℓ As → Type (ℓ ⊔ ℓsup arity ls)
Universalⁿ {0}                         P = P
Universalⁿ {1}           {As = A}      P = Π[ a ꞉ A ] P a
Universalⁿ {suc (suc _)} {As = A , As} P = Π[ a ꞉ A ] Universalⁿ (P a)
{-# INLINE Universalⁿ #-}

syntax Universalⁿ P = Πⁿ[ P ]

Universal = Universalⁿ {arity = 1}
syntax Universal P = Π[ P ]
Universal¹ = Universalⁿ {arity = 1}
syntax Universal¹ P = Π¹[ P ]
Universal² = Universalⁿ {arity = 2}
syntax Universal² P = Π²[ P ]
Universal³ = Universalⁿ {arity = 3}
syntax Universal³ P = Π³[ P ]
Universal⁴ = Universalⁿ {arity = 4}
syntax Universal⁴ P = Π⁴[ P ]
Universal⁵ = Universalⁿ {arity = 5}
syntax Universal⁵ P = Π⁵[ P ]

infix 10 IUniversal IUniversal¹ IUniversal² IUniversal³ IUniversal⁴ IUniversal⁵

IUniversalⁿ : {ls : Levels arity} {As : Types arity ls} → Corr arity ℓ As → Type (ℓ ⊔ ℓsup arity ls)
IUniversalⁿ {0}                         P = P
IUniversalⁿ {1}           {As = A}      P = ∀{a} → P a
IUniversalⁿ {suc (suc _)} {As = A , As} P = ∀{a} → IUniversalⁿ (P a)
{-# INLINE IUniversalⁿ #-}

syntax IUniversalⁿ P = ∀ⁿ[ P ]

IUniversal = IUniversalⁿ {arity = 1}
syntax IUniversal P = ∀[ P ]
IUniversal¹ = IUniversalⁿ {arity = 1}
syntax IUniversal¹ P = ∀¹[ P ]
IUniversal² = IUniversalⁿ {arity = 2}
syntax IUniversal² P = ∀²[ P ]
IUniversal³ = IUniversalⁿ {arity = 3}
syntax IUniversal³ P = ∀³[ P ]
IUniversal⁴ = IUniversalⁿ {arity = 4}
syntax IUniversal⁴ P = ∀⁴[ P ]
IUniversal⁵ = IUniversalⁿ {arity = 5}
syntax IUniversal⁵ P = ∀⁵[ P ]

_⇒ⁿ_ : {ls : Levels arity} {As : Types arity ls} → Corr arity ℓ As → Corr arity ℓ′ As → Corr arity (ℓ ⊔ ℓ′) As
_⇒ⁿ_ {0}           P Q = P → Q
_⇒ⁿ_ {1}           P Q = λ x → P x → Q x
_⇒ⁿ_ {suc (suc _)} P Q = λ x → P x ⇒ⁿ Q x

_⇒⁰_ = _⇒ⁿ_ {arity = 0}
_⇒_  = _⇒ⁿ_ {arity = 1}
_⇒¹_ = _⇒ⁿ_ {arity = 1}
_⇒²_ = _⇒ⁿ_ {arity = 2}
_⇒³_ = _⇒ⁿ_ {arity = 3}
_⇒⁴_ = _⇒ⁿ_ {arity = 4}
_⇒⁵_ = _⇒ⁿ_ {arity = 5}


-- Binary homogeneous correspondences

Reflexive : Corr 2 ℓ (A , A) → Type _
Reflexive _~_ = ∀ {x} → x ~ x

Symmetric : Corr 2 ℓ (A , A) → Type _
Symmetric _~_ = ∀ {x y} → (x ~ y) → (y ~ x)

Transitive : Corr 2 ℓ (A , A) → Type _
Transitive _~_ = ∀ {x y z} → (x ~ y) → (y ~ z) → (x ~ z)

record Equivalence (_~_ : Corr 2 ℓ (A , A)) : Type (level-of-type A ⊔ ℓ) where
  field
    reflᶜ : Reflexive _~_
    symᶜ  : Symmetric _~_
    _∙ᶜ_  : Transitive _~_

record is-congruence (_~_ : Corr 2 ℓ (A , A)) : Type (level-of-type A ⊔ ℓ) where
  field
    equivalenceᶜ : Equivalence _~_
    instance
      has-propᶜ    : ∀ {x y} → is-prop (x ~ y)
  open Equivalence equivalenceᶜ public
