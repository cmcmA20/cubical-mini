{-# OPTIONS --safe #-}
module Foundations.Notation.Involutivity where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Duality

private variable
  ℓᵃ ℓᵇ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ : Level}
  (I : A → B → 𝒰 ℓ) (O : B → A → 𝒰 ℓ′) where

  GInvolutivity
    : (s₁ : Duality I O) (s₂ : Duality O I)
      {x : A} {y : B} (i : I x y)
    → 𝒰 ℓ
  GInvolutivity s₁ s₂ i = s₂ (s₁ i) ＝ i

  record GInvol ⦃ s₁ : Dual I O ⦄ ⦃ s₂ : Dual O I ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ′) where
    no-eta-equality
    field invol : ∀ {x y} (i : I x y) → GInvolutivity (s₁ ._ᵒᵖ) (s₂ ._ᵒᵖ) i

open GInvol ⦃ ... ⦄ public


-- homogeneous correspondence involutivity
HInvol : (R : A → A → 𝒰 ℓ) ⦃ s : Sym R ⦄ → 𝒰 _
HInvol R = GInvol R R


-- function involutivity
module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where
  Involutivity : (s : A → A) (x : A) → 𝒰 ℓᵃ
  Involutivity s x = s (s x) ＝ x

  record Invol ⦃ s : Has-unary-op A ⦄ : 𝒰 ℓᵃ where
    no-eta-equality
    field minv-invol : ∀ x → Involutivity (s .minv) x

open Invol ⦃ ... ⦄ public

instance
  Invol→HInvol
    : ⦃ s : Has-unary-op A ⦄ ⦃ _ : Invol A ⦄
    → HInvol {A = ⊤} (λ _ _ → A)
  Invol→HInvol .invol = minv-invol
  {-# INCOHERENT Invol→HInvol #-}
