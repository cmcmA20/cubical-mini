{-# OPTIONS --safe #-}
module Structures.IdentitySystem.Interface where

open import Foundations.Base
  hiding (J; J-refl)
open import Foundations.HLevel.Base
open import Foundations.Equiv

import Structures.IdentitySystem.Base as I
open I public
  using ( is-identity-system ; to-path ; to-path-over ; to-path-refl ; identity-system-gives-path
        ; identity-system→is-of-hlevel ; transfer-identity-system )
import Structures.IdentitySystem.Strict as IS
open IS public
  using (set-identity-is-prop)

private variable ℓ″ : Level

module
  IdS {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {refl : ∀ a → R a a}
      (rr : is-identity-system R refl)
  where

  private variable a : A

  J : (P : (b : A) → R a b → Type ℓ″) → P a (refl a) → {b : A} (s : R a b) → P b s
  J = I.J rr

  J-refl
    : (P : ∀ b → R a b → Type ℓ″) (x : P a (refl a))
    → J P x (refl a) ＝ x
  J-refl = I.J-refl rr

  module _ {a b} where open Equiv (identity-system-gives-path rr {a} {b}) public

  to-refl : to-path rr (refl a) ＝ λ _ → a
  to-refl = to-path-refl rr

  from-refl : from (λ _ → a) ＝ refl a
  from-refl = transport-refl (refl _)

  hlevel′ : ∀ n → (∀ x y → is-of-hlevel n (R x y)) → is-of-hlevel (suc n) A
  hlevel′ n = identity-system→is-of-hlevel n rr


module IdSS
  {ℓ ℓ′} {A : Type ℓ}
  {R : A → A → Type ℓ′} {r : ∀ a → R a a}
  (ids : is-identity-system R r)
  (set : is-set A)
  where

  private variable a : A

  K : (P : R a a → Type ℓ″) → P (r a) → ∀ s → P s
  K = IS.K ids set

  K-refl : (P : R a a → Type ℓ″) (x : P (r a)) → K P x (r a) ＝ x
  K-refl = IS.K-refl ids set

  -- TODO rename and fix signature
  instance
    R-HLevel : ∀ {a b} {n} → is-of-hlevel (suc n) (R a b)
    R-HLevel = is-prop→is-of-hlevel-suc (set-identity-is-prop ids set)
