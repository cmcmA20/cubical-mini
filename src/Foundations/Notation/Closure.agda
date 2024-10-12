{-# OPTIONS --safe #-}
module Foundations.Notation.Closure where

open import Foundations.Notation.Underlying
open import Foundations.Prim.Type

private variable ℓ ℓ′ : Level

record Closure-Π {ℓᵃ} (A : 𝒰 ℓᵃ) : Typeω where
  infixr 6 Π[_]
  field
    ℓ-total-Π : Level
    Π[_]      : A → Type ℓ-total-Π
open Closure-Π ⦃ ... ⦄ public
{-# DISPLAY Closure-Π.Π[_] _ f = Π[ f ] #-}

record Closure-∀ {ℓᵃ} (A : 𝒰 ℓᵃ) : Typeω where
  infixr 6 ∀[_]
  field
    ℓ-total-∀ : Level
    ∀[_]      : A → Type ℓ-total-∀
open Closure-∀ ⦃ ... ⦄ public
{-# DISPLAY Closure-∀.∀[_] _ f = ∀[ f ] #-}

record Closure-∀ᴱ {ℓᵃ} (A : 𝒰 ℓᵃ) : Typeω where
  infixr 6 ∀ᴱ[_]
  field
    ℓ-total-∀ᴱ : Level
    ∀ᴱ[_]      : @0 A → Type ℓ-total-∀ᴱ
open Closure-∀ᴱ ⦃ ... ⦄ public
{-# DISPLAY Closure-∀ᴱ.∀ᴱ[_] _ f = ∀ᴱ[ f ] #-}

-- closing over free variables of an expression using a sigma quantifier
-- is called a total space
record Total-Σ {ℓᵃ} (A : 𝒰 ℓᵃ) : Typeω where
  infixr 6 Σ[_]
  field
    ℓ-total-Σ : Level
    Σ[_]      : A → Type ℓ-total-Σ
open Total-Σ ⦃ ... ⦄ public
{-# DISPLAY Total-Σ.Σ[_] _ f = Σ[ f ] #-}

instance
  Closure-Π-Type : Closure-Π (Type ℓ)
  Closure-Π-Type {ℓ} .ℓ-total-Π = ℓ
  Closure-Π-Type .Π[_] f = f
  {-# OVERLAPPING Closure-Π-Type #-}

  Closure-Π-Underlying : {A : Type ℓ} ⦃ u : Underlying A ⦄ → Closure-Π A
  Closure-Π-Underlying ⦃ u ⦄ .ℓ-total-Π = u .ℓ-underlying
  Closure-Π-Underlying .Π[_] = ⌞_⌟
  {-# INCOHERENT Closure-Π-Underlying #-}

  Closure-∀-Type : Closure-∀ (Type ℓ)
  Closure-∀-Type {ℓ} .ℓ-total-∀ = ℓ
  Closure-∀-Type .∀[_] f = f
  {-# OVERLAPPING Closure-∀-Type #-}

  Closure-∀-Underlying : {A : Type ℓ} ⦃ u : Underlying A ⦄ → Closure-∀ A
  Closure-∀-Underlying ⦃ u ⦄ .ℓ-total-∀ = u .ℓ-underlying
  Closure-∀-Underlying .∀[_] = ⌞_⌟
  {-# INCOHERENT Closure-∀-Underlying #-}

  @0 Closure-∀ᴱ-Type : Closure-∀ᴱ (Type ℓ)
  Closure-∀ᴱ-Type {ℓ} .ℓ-total-∀ᴱ = ℓ
  Closure-∀ᴱ-Type .∀ᴱ[_] f = f
  {-# OVERLAPPING Closure-∀ᴱ-Type #-}

  @0 Closure-∀ᴱ-Underlying : {A : Type ℓ} ⦃ u : Underlying A ⦄ → Closure-∀ᴱ A
  Closure-∀ᴱ-Underlying ⦃ u ⦄ .ℓ-total-∀ᴱ = u .ℓ-underlying
  Closure-∀ᴱ-Underlying .∀ᴱ[_] z = ⌞ z ⌟
  {-# INCOHERENT Closure-∀ᴱ-Underlying #-}

  Total-Σ-Type : Total-Σ (Type ℓ)
  Total-Σ-Type {ℓ} .ℓ-total-Σ = ℓ
  Total-Σ-Type .Σ[_] f = f
  {-# OVERLAPPING Total-Σ-Type #-}

  Total-Σ-Underlying : {A : Type ℓ} ⦃ u : Underlying A ⦄ → Total-Σ A
  Total-Σ-Underlying ⦃ u ⦄ .ℓ-total-Σ = u .ℓ-underlying
  Total-Σ-Underlying .Σ[_] = ⌞_⌟
  {-# INCOHERENT Total-Σ-Underlying #-}
