{-# OPTIONS --safe #-}
module Structures.IdentitySystem.Interface where

open import Foundations.Base
  hiding (J; J-refl)
open import Foundations.HLevel.Base
open import Foundations.Equiv

import Structures.IdentitySystem.Base as I
import Structures.IdentitySystem.Strict as IS

module
  IdS {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {refl : ∀ a → R a a}
      (rr : I.is-identity-system R refl)
  where

  J : ∀ {ℓ a} (P : (b : A) → R a b → Type ℓ) → P a (refl a) → {b : A} (s : R a b) → P b s
  J = I.J rr

  J-refl
    : ∀ {ℓ a} (P : ∀ b → R a b → Type ℓ) → (x : P a (refl a))
    → J P x (refl a) ＝ x
  J-refl = I.J-refl rr

  module _ {a b} where open Equiv (I.identity-system-gives-path rr {a} {b}) public

  to-refl : ∀ {a} → I.to-path rr (refl a) ＝ λ _ → a
  to-refl = I.to-path-refl rr

  from-refl : ∀ {a} → from (λ _ → a) ＝ refl a
  from-refl = transport-refl (refl _)

  hlevel′ : ∀ n → (∀ x y → is-of-hlevel n (R x y)) → is-of-hlevel (suc n) A
  hlevel′ n = I.identity-system→is-of-hlevel n rr


module IdSS
  {ℓ ℓ′ ℓ″} {A : Type ℓ}
  {R : A → A → Type ℓ′} {r : ∀ a → R a a}
  (ids : I.is-identity-system R r)
  (set : is-set A)
  where

  K : ∀ {a} → (P : R a a → Type ℓ″) → P (r a) → ∀ s → P s
  K = IS.K ids set

  K-refl : ∀ {a} → (P : R a a → Type ℓ″) → (x : P (r a)) → K P x (r a) ＝ x
  K-refl = IS.K-refl ids set

  -- TODO rename and fix signature
  instance
    R-HLevel : ∀ {a b} {n} → is-of-hlevel (suc n) (R a b)
    R-HLevel = is-prop→is-of-hlevel-suc (IS.set-identity-is-prop ids set)
