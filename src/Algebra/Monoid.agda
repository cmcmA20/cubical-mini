
module Algebra.Monoid where

open import Foundations.Base

open import Algebra.Semigroup

private variable
  ℓ : Level
  A : 𝒰 ℓ

record is-monoid {A : 𝒰 ℓ} (𝟏 : A) (_⋆_ : A → A → A) : Type ℓ where
  field
    has-is-semigroup : is-semigroup _⋆_

  open is-semigroup has-is-semigroup public

  field
    idl : {x : A} → 𝟏 ⋆ x ＝ x
    idr : {x : A} → x ⋆ 𝟏 ＝ x

    id-coh : {x y : A}
      → ap (_⋆ y) idr
      ＝ sym (associative has-is-semigroup x 𝟏 y)
      ∙ ap (x ⋆_) idl

open is-monoid public

record Monoid-on (A : 𝒰 ℓ) : 𝒰 ℓ where
  field
    𝟏   : A
    _⋆_ : A → A → A

    has-is-monoid : is-monoid 𝟏 _⋆_

Monoid : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
Monoid ℓ = Σ[ A ꞉ 𝒰 ℓ ] Monoid-on A

-- is-set-is-monoid :
--   {𝟏   : A}
--   {_⋆_ : A → A → A}
--        → is-set (is-monoid 𝟏 _⋆_)
-- is-set-is-monoid = {!   !}