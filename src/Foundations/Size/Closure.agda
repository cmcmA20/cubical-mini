{-# OPTIONS --safe #-}
module Foundations.Size.Closure where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Pi.Properties
open import Foundations.Sigma.Properties
open import Foundations.Size.Base

private variable ℓ ℓ′ ℓ″ ℓ‴ : Level

≃→is-of-size : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
             → A ≃ B
             → is-of-size ℓ″ A → is-of-size ℓ″ B
≃→is-of-size e = second (_∙ e)

≅→is-of-size : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
             → A ≅ B
             → is-of-size ℓ″ A → is-of-size ℓ″ B
≅→is-of-size e = second (_∙ ≅→≃ e)

Σ-is-of-size : {A : 𝒰 ℓ} {B : A → 𝒰 ℓ′}
             → is-of-size ℓ″ A
             → ((a : A) → is-of-size ℓ‴ (B a))
             → is-of-size (ℓ″ ⊔ ℓ‴) (Σ[ x ꞉ A ] B x)
Σ-is-of-size {ℓ‴} (X , e) sa
  = Σ[ x ꞉ X ] ⌞ sa (e $ x) ⌟
  , Σ-ap e λ z → resizing-cond (sa (e $ z))

×-is-of-size : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
             → is-of-size ℓ″ A
             → is-of-size ℓ‴ B
             → is-of-size (ℓ″ ⊔ ℓ‴) (A × B)
×-is-of-size sa sb = Σ-is-of-size sa λ _ → sb

Π-is-of-size : {A : 𝒰 ℓ} {B : A → 𝒰 ℓ′}
             → is-of-size ℓ″ A
             → ((a : A) → is-of-size ℓ‴ (B a))
             → is-of-size (ℓ″ ⊔ ℓ‴) (Π[ x ꞉ A ] B x)
Π-is-of-size {ℓ‴} (X , e) sa
  = Π[ x ꞉ X ] ⌞ sa (e $ x) ⌟
  , Π-ap e λ z → resizing-cond (sa (e $ z))


instance
  Size-Π
    : {A : Type ℓ} {B : A → Type ℓ′}
      ⦃ sa : Size ℓ″ A ⦄ ⦃ sb : ∀{a} → Size ℓ‴ (B a) ⦄
    → Size (ℓ″ ⊔ ℓ‴) (Π[ x ꞉ A ] B x)
  Size-Π {ℓ″} {ℓ‴} .Size.has-of-size = Π-is-of-size (size ℓ″) λ _ → size ℓ‴
  {-# OVERLAPPABLE Size-Π #-}

  Size-Σ
    : {A : Type ℓ} {B : A → Type ℓ′}
      ⦃ sa : Size ℓ″ A ⦄ ⦃ sb : ∀{a} → Size ℓ‴ (B a) ⦄
    → Size (ℓ″ ⊔ ℓ‴) (Σ[ x ꞉ A ] B x)
  Size-Σ {ℓ″} {ℓ‴} .Size.has-of-size = Σ-is-of-size (size ℓ″) λ _ → size ℓ‴
  {-# OVERLAPPABLE Size-Σ #-}

  Size-Lift : {A : Type ℓ} ⦃ hl : Size ℓ′ A ⦄ → Size ℓ′ (Lift ℓ″ A)
  Size-Lift {ℓ′} {A} .Size.has-of-size = second (_∙ lift≃id ⁻¹) (size ℓ′)


-- Automation

≃→is-of-size! : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} → A ≃ B → ⦃ Size ℓ″ A ⦄ → is-of-size ℓ″ B
≃→is-of-size! e = ≃→is-of-size e (size _)

≅→is-of-size! : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} → A ≅ B → ⦃ Size ℓ″ A ⦄ → is-of-size ℓ″ B
≅→is-of-size! e = ≅→is-of-size e (size _)
