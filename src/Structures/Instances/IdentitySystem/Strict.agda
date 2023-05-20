{-# OPTIONS --safe #-}
module Structures.Instances.IdentitySystem.Strict where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.HLevel

open import Structures.Instances.IdentitySystem.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ′
  R : A → A → Type ℓ′
  r : ∀ a → R a a

set-identity-is-prop
  : ∀ {r : (a : A) → R a a} {a b : A}
  → is-identity-system R r
  → is-set A
  → is-prop (R a b)
set-identity-is-prop {R} {a} {b} ids set =
  is-of-hlevel-≃ 1 (identity-system-gives-path ids) (set a b)

IdsK
  : {r : (a : A) → R a a} {a : A}
  → is-identity-system R r
  → is-set A
  → (P : R a a → Type ℓ″) → P (r a) → ∀ s → P s
IdsK {r} {a} ids set P pr s =
  transport (λ i → P (set-identity-is-prop ids set (r a) s i)) pr

IdsK-refl
  : {r : ∀ a → R a a} {a : A}
  → (ids : is-identity-system R r)
  → (set : is-set A)
  → (P : R a a → Type ℓ″)
  → (p : P (r a))
  → IdsK ids set P p (r a) ＝ p
IdsK-refl {R} {r} {a} ids set P p =
  transport (λ i → P (set-identity-is-prop ids set (r a) (r a) i)) p ＝⟨⟩
  subst P (set-identity-is-prop ids set (r a) (r a)) p               ＝⟨ ap (λ ϕ → subst P ϕ p) lemma ⟩
  transport (λ i → P (r a)) p                                        ＝⟨ transport-refl p ⟩
  p ∎
  where
    lemma : set-identity-is-prop ids set (r a) (r a) ＝ refl
    lemma = is-prop→is-set (set-identity-is-prop ids set) (r a) (r a) _ _

module StrictIds
  {R : A → A → Type ℓ′} {r : ∀ a → R a a}
  (ids : is-identity-system R r)
  (set : is-set A)
  where

  K : ∀ {a} → (P : R a a → Type ℓ″) → P (r a) → ∀ s → P s
  K = IdsK ids set

  K-refl : ∀ {a} → (P : R a a → Type ℓ″) → (x : P (r a)) → K P x (r a) ＝ x
  K-refl = IdsK-refl ids set

  instance
    R-H-level : ∀ {a b} {n} → H-Level (suc n) (R a b)
    R-H-level = prop-instance (set-identity-is-prop ids set)
