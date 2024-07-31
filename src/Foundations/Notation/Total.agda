{-# OPTIONS --safe #-}
module Foundations.Notation.Total where

open import Foundations.Notation.Underlying
open import Foundations.Prim.Type

private variable ℓ ℓ′ : Level

record Total-Π {ℓᵃ} (A : 𝒰 ℓᵃ) : Typeω where
  infixr 6 Π[_]
  field
    ℓ-total-Π : Level
    Π[_]      : A → Type ℓ-total-Π
open Total-Π ⦃ ... ⦄ public

record Total-∀ {ℓᵃ} (A : 𝒰 ℓᵃ) : Typeω where
  infixr 6 ∀[_]
  field
    ℓ-total-∀ : Level
    ∀[_]      : A → Type ℓ-total-∀
open Total-∀ ⦃ ... ⦄ public

record Total-Σ {ℓᵃ} (A : 𝒰 ℓᵃ) : Typeω where
  infixr 6 Σ[_]
  field
    ℓ-total-Σ : Level
    Σ[_]      : A → Type ℓ-total-Σ
open Total-Σ ⦃ ... ⦄ public

instance
  Total-Π-Type : Total-Π (Type ℓ)
  Total-Π-Type {ℓ} .ℓ-total-Π = ℓ
  Total-Π-Type .Π[_] f = f
  {-# OVERLAPPING Total-Π-Type #-}

  Total-Π-Underlying : {A : Type ℓ} ⦃ u : Underlying A ⦄ → Total-Π A
  Total-Π-Underlying ⦃ u ⦄ .ℓ-total-Π = u .ℓ-underlying
  Total-Π-Underlying .Π[_] = ⌞_⌟
  {-# INCOHERENT Total-Π-Underlying #-}

  Total-∀-Type : Total-∀ (Type ℓ)
  Total-∀-Type {ℓ} .ℓ-total-∀ = ℓ
  Total-∀-Type .∀[_] f = f
  {-# OVERLAPPING Total-∀-Type #-}

  Total-∀-Underlying : {A : Type ℓ} ⦃ u : Underlying A ⦄ → Total-∀ A
  Total-∀-Underlying ⦃ u ⦄ .ℓ-total-∀ = u .ℓ-underlying
  Total-∀-Underlying .∀[_] = ⌞_⌟
  {-# INCOHERENT Total-∀-Underlying #-}

  Total-Σ-Type : Total-Σ (Type ℓ)
  Total-Σ-Type {ℓ} .ℓ-total-Σ = ℓ
  Total-Σ-Type .Σ[_] f = f
  {-# OVERLAPPING Total-Σ-Type #-}

  Total-Σ-Underlying : {A : Type ℓ} ⦃ u : Underlying A ⦄ → Total-Σ A
  Total-Σ-Underlying ⦃ u ⦄ .ℓ-total-Σ = u .ℓ-underlying
  Total-Σ-Underlying .Σ[_] = ⌞_⌟
  {-# INCOHERENT Total-Σ-Underlying #-}
