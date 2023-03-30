{-# OPTIONS --safe #-}
module Cubical.HITs.Int.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.Int
  renaming (ℤ to ℤᵢ; neg to negᵢ; isSetℤ to isSetℤᵢ; discreteℤ to discreteℤᵢ)

open import Cubical.HITs.Int.Base

open import Cubical.Relation.Nullary

succEquiv : ℤ ≃ ℤ
succEquiv = isoToEquiv (iso succ pred succPred predSucc)
  where
  succPred : ∀ m → succ (pred m) ≡ m
  succPred (neg _)       = refl
  succPred (pos zero)    = 0₋≡0₊
  succPred (pos (suc _)) = refl
  succPred (0₋≡0₊ i) j = 0₋≡0₊ (i ∧ j)

  predSucc : ∀ m → pred (succ m) ≡ m
  predSucc (neg zero)    = sym 0₋≡0₊
  predSucc (neg (suc _)) = refl
  predSucc (pos _)       = refl
  predSucc (0₋≡0₊ i) j = sym 0₋≡0₊ (~ i ∧ j)

ℤ≃ℤᵢ : ℤ ≃ ℤᵢ
ℤ≃ℤᵢ = isoToEquiv (iso to from li ri)
  where
  to : ℤ → ℤᵢ
  to (neg zero)    = pos 0
  to (neg (suc n)) = negsuc n
  to (pos n)       = pos n
  to (0₋≡0₊ _) = pos zero

  from : ℤᵢ → ℤ
  from (pos    n) = pos n
  from (negsuc n) = neg (suc n)

  li : (b : ℤᵢ) → to (from b) ≡ b
  li (pos _)    = refl
  li (negsuc _) = refl

  ri : (a : ℤ) → from (to a) ≡ a
  ri (neg zero)    = sym 0₋≡0₊
  ri (neg (suc _)) = refl
  ri (pos _)       = refl
  ri (0₋≡0₊ i) j = 0₋≡0₊ (i ∨ ~ j)

discreteℤ : Discrete ℤ
discreteℤ = EquivPresDiscrete (invEquiv ℤ≃ℤᵢ) discreteℤᵢ

isSetℤ : isSet ℤ
isSetℤ = Discrete→isSet discreteℤ
