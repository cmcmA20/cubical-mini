{-# OPTIONS --safe #-}
module Data.Id.Properties where

open import Foundations.Base
  renaming (J to Jₜ)
open import Foundations.Equiv
open import Foundations.Path

open import Structures.IdentitySystem

open import Data.Id.Base

private variable
  ℓᵃ : Level
  A : 𝒰 ℓᵃ
  x y z w : A

Id-identity-system : is-identity-system (_＝ˢ_ {A = A}) (λ _ → reflˢ)
Id-identity-system .to-path p = p _ refl
Id-identity-system .to-path-over f = fun-ext λ _ → fun-ext λ q →
  Jₜ (λ y p → ＜ sym p ／ (λ i → y ＝ f _ refl i) ＼ f _ (sym p) ＞)
     (λ i j → f _ refl (i ∧ j)) (sym q)

Id≃path : (x ＝ˢ y) ≃ (x ＝ y)
Id≃path = identity-system-gives-path Id-identity-system

module Id≃path {ℓ} {A : Type ℓ} = IdS (Id-identity-system {A = A})

-- excellent reduction behaviour

∙ˢ-id-l : (p : x ＝ˢ y) → reflˢ ∙ˢ p ＝ p
∙ˢ-id-l _ = refl

∙ˢ-id-r : (p : x ＝ˢ y) → p ∙ˢ reflˢ ＝ p
∙ˢ-id-r _ = refl

∙ˢ-assoc
  : (p : x ＝ˢ y) (q : y ＝ˢ z) (r : z ＝ˢ w)
  → p ∙ˢ (q ∙ˢ r) ＝ (p ∙ˢ q) ∙ˢ r
∙ˢ-assoc _ _ _ = refl
