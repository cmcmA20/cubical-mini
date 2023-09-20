
module Algebra.Group where

open import Foundations.Base

open import Algebra.Monoid

private variable
  ℓ : Level
  A : 𝒰 ℓ
  x y : A

record is-group {ℓ} {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field
    𝟏   : A
    _⁻¹ : A → A

  infixl 30 _⁻¹

  field
    has-is-monoid : is-monoid 𝟏 _⋆_

  open is-monoid has-is-monoid public

  field
    inversel      : x ⁻¹ ⋆ x ＝ 𝟏
    inverser      : x ⋆ x ⁻¹ ＝ 𝟏
    top⁻¹-coh     :
      ap (x ⋆_) (inversel {x = x}) ∙ idr has-is-monoid
        ＝
      associative has-is-monoid _ _ _
        ∙ ap (_⋆ x) inverser ∙ idl has-is-monoid
        -- ap (_⋆ x) {! idr has-is-monoid  !} ∙ {!   !}


record Group-on {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  field
    _⋆_          : A → A → A
    has-is-group : is-group _⋆_

  infixr 20 _⋆_

  open is-group has-is-group public

Group : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
Group ℓ = Σ[ A ꞉ 𝒰 ℓ ] Group-on A
