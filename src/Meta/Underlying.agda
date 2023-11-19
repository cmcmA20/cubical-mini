{-# OPTIONS --safe #-}
module Meta.Underlying where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Nat.Base

record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟⁰          : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ public

{-# DISPLAY Underlying.⌞_⌟⁰ f x = ⌞ x ⌟⁰ #-}

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : A → Type ℓ′
  P : Type ℓ′

instance
  Underlying-Σ : ⦃ ua : Underlying A ⦄ → Underlying (Σ A B)
  Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Σ .⌞_⌟⁰ x = ⌞ x .fst ⌟⁰

  Underlying-Type : Underlying (Type ℓ)
  Underlying-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟⁰ x = x

  Underlying-Lift : ⦃ ua : Underlying A ⦄ → Underlying (Lift ℓ′ A)
  Underlying-Lift ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Lift .⌞_⌟⁰ x = ⌞ x .lower ⌟⁰


infix 5 _∈_
_∈_ : ⦃ u : Underlying P ⦄ → A → (A → P) → Type _
x ∈ P = ⌞ P x ⌟⁰

infix 5 _∉_
_∉_ : ⦃ u : Underlying P ⦄ → A → (A → P) → Type _
x ∉ P = ¬ x ∈ P

_⊆_ : ⦃ u : Underlying P ⦄ → (A → P) → (A → P) → Type _
U ⊆ V = {x : _} → x ∈ U → x ∈ V
