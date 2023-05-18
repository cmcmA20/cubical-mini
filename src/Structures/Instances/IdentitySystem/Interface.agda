{-# OPTIONS --safe #-}
module Structures.Instances.IdentitySystem.Interface where

open import Foundations.Base
  hiding (J; J-refl)
open import Foundations.HLevel.Base
open import Foundations.Equiv

open import Structures.Instances.IdentitySystem.Base

module
  Ids {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {refl : ∀ a → R a a}
      (rr : is-identity-system R refl)
  where

  J : ∀ {ℓ a} (P : (b : A) → R a b → Type ℓ) → P a (refl a) → {b : A} (s : R a b) → P b s
  J = IdsJ rr

  J-refl
    : ∀ {ℓ a} (P : ∀ b → R a b → Type ℓ) → (x : P a (refl a))
    → J P x (refl a) ＝ x
  J-refl = IdsJ-refl rr

  module _ {a b} where open Equiv (identity-system-gives-path rr {a} {b}) public

  to-refl : ∀ {a} → to-path rr (refl a) ＝ λ _ → a
  to-refl = to-path-refl rr

  from-refl : ∀ {a} → from (λ _ → a) ＝ refl a
  from-refl = transport-refl (refl _)

  hlevel : ∀ n → (∀ x y → is-of-hlevel n (R x y)) → is-of-hlevel (suc n) A
  hlevel n = identity-system→hlevel n rr
