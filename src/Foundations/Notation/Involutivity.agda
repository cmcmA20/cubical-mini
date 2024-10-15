{-# OPTIONS --safe #-}
module Foundations.Notation.Involutivity where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Duality

private variable
  ℓ : Level
  A : 𝒰 ℓ

module _
  {ℓa ℓb ℓh} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  (I : A → B → 𝒰 ℓh) (O : B → A → 𝒰 ℓh) where

  GInvolutivity
    : {x : A} {y : B} (i : I x y)
      (s₁ : Duality I O i) (s₂ : Duality O I s₁)
    → 𝒰 ℓh
  GInvolutivity i s₁ s₂ = s₂ ＝ i

  record GInvol ⦃ s₁ : Dual I O ⦄ ⦃ s₂ : Dual O I ⦄ : 𝒰 (ℓa ⊔ ℓb ⊔ ℓh) where
    no-eta-equality
    field invol : ∀ {x y} (i : I x y) → GInvolutivity i (s₁ ._ᵒᵖ i) (s₂ ._ᵒᵖ (s₁ ._ᵒᵖ i))

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
