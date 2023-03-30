-- got it from 1Lab
{-# OPTIONS --safe #-}
module Cubical.Foundations.IdentitySystem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma.Properties

record isIdentitySystem {ℓ ℓ′} {A : Type ℓ}
  (R : A → A → Type ℓ′) (rfl : ∀ a → R a a)
  : Type (ℓ-max ℓ ℓ′) where
  no-eta-equality
  field
    toPath     : ∀ {a b} → R a b → a ≡ b
    toPathOver : ∀ {a b} → (p : R a b)
               → PathP (λ i → R a (toPath p i)) (rfl a) p

  isContrTotal : ∀ {a} → isContr (Σ A (R a))
  isContrTotal = ( _ , rfl _ )
                 , λ x i → ( toPath     (x .snd) i )
                           , toPathOver (x .snd) i
open isIdentitySystem

IdsJ
  : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a} {a : A}
  → isIdentitySystem R r
  → (P : ∀ b → R a b → Type ℓ″)
  → P a (r a)
  → ∀ {b} s → P b s
IdsJ ids P pr s = transport (λ i → P (ids .toPath s i) (ids .toPathOver s i)) pr

toPathReflCoh
  : ∀ {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a}
  → (ids : isIdentitySystem R r)
  → (a : A)
  → ΣPathP (ids .toPath (r a) , ids .toPathOver (r a)) ≡ refl
toPathReflCoh {r = r} ids a =
  isContr→isOfHLevel 2 (isContrTotal ids) _ _ (ΣPathP (ids .toPath (r a) , ids .toPathOver (r a))) refl

toPathRefl
  : ∀ {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a} {a : A}
  → (ids : isIdentitySystem R r)
  → ids .isIdentitySystem.toPath (r a) ≡ refl
toPathRefl ids = cong (cong fst) (toPathReflCoh ids _)

identitySystem≃PathSpace
  : ∀ {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a}
  → isIdentitySystem R r
  → ∀ {a b} → R a b ≃ (a ≡ b)
identitySystem≃PathSpace {R = R} {r = r} ids {a = a} =
  isoToEquiv (iso (ids .toPath) from ri li)
  where
  from : ∀ {a b} → a ≡ b → R a b
  from {a = a} p = transport (λ i → R a (p i)) (r a)

  ri : ∀ {a b} → section (ids .toPath {a} {b}) from
  ri = J (λ y p → ids .toPath (from p) ≡ p) (cong (ids .toPath) (transportRefl _) ∙ toPathRefl ids)

  li : ∀ {a b} → retract (ids .toPath {a} {b}) from
  li = IdsJ ids (λ _ p → from (ids .toPath p) ≡ p) (cong from (toPathRefl ids) ∙ transportRefl _)
