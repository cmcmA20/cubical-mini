{-# OPTIONS --safe #-}
module Data.Reflects.Sigma where

open import Foundations.Prelude
open import Meta.Effect

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Unit.Base as ⊤
open import Data.Sum as Sum hiding (dmap)
open import Data.Maybe as Maybe

data ReflectsΣ {ℓ ℓ′} {A : 𝒰 ℓ} (P : A → 𝒰 ℓ′) : Maybe A → 𝒰 (ℓ ⊔ ℓ′) where
  ofʲ : (x : A) → P x → ReflectsΣ P (just x)
  ofⁿ : (∀ x → ¬ P x) → ReflectsΣ P nothing

private variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  P : A → Type ℓ′
  Q : A → Type ℓ″
  m : Maybe A

dmap : (∀ x → P x → Q x)
     → (∀ x → ¬ (P x) → ¬ (Q x)) -- is this general enough?
     → ReflectsΣ P m → ReflectsΣ Q m
dmap to fro (ofʲ x px) = ofʲ x (to x px)
dmap to fro (ofⁿ nx)   = ofⁿ λ x → fro x (nx x)

reflectsΣ-map : {A : Type ℓᵃ} {B : Type ℓᵇ}
                {P : A → Type ℓ′} {Q : B → Type ℓ″}
                {m : Maybe A} {f : A → B}
                (g : B → A)
              → (∀ x → P x → Q (f x))
              → (∀ y → ¬ P (g y) → ¬ Q y)
              -- + some condition on f cancelling g ?
              → ReflectsΣ P m
              → ReflectsΣ Q (mapₘ f m)
reflectsΣ-map {f} _ pq npq (ofʲ x px) = ofʲ (f x) (pq x px)
reflectsΣ-map     g pq npq (ofⁿ nx)   = ofⁿ λ y → npq y (nx (g y))

reflectsΣ-alter : {A : Type ℓᵃ} {B : Type ℓᵇ}
                  {P : A → Type ℓ′} {Q : B → Type ℓ′}
                  {ma : Maybe A} {mb : Maybe B}
                → ReflectsΣ P ma
                → ReflectsΣ Q mb
                → ReflectsΣ [ P , Q ]ᵤ (ma <+> mb)
reflectsΣ-alter (ofʲ x px)  rb        = ofʲ (inl x) px
reflectsΣ-alter (ofⁿ nx)   (ofʲ y qy) = ofʲ (inr y) qy
reflectsΣ-alter (ofⁿ nx)   (ofⁿ ny)   = ofⁿ (Sum.elim nx ny)
