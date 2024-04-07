{-# OPTIONS --safe #-}
module Data.Id.Properties where

open import Foundations.Base
  renaming ( _＝_ to _＝ₚ_
           ; refl to reflₚ
           ; sym  to symₚ
           ; _∙_  to _∙ₚ_
           ; J    to Jₜ )
open import Foundations.Equiv
open import Foundations.Path

open import Structures.IdentitySystem

open import Data.Id.Base

private variable
  ℓᵃ : Level
  A : 𝒰 ℓᵃ
  x y z w : A

Id-identity-system : is-identity-system (_＝_ {A = A}) (λ _ → refl)
Id-identity-system .to-path p = p _ reflₚ
Id-identity-system .to-path-over f = fun-ext λ _ → fun-ext λ q →
  Jₜ (λ y p → ＜ symₚ p ／ (λ i → y ＝ₚ f _ reflₚ i) ＼ f _ (symₚ p) ＞)
     ((λ i j → f _ reflₚ (i ∧ j))) (symₚ q)

Id≃path : (x ＝ y) ≃ (x ＝ₚ y)
Id≃path = identity-system-gives-path Id-identity-system

module Id≃path {ℓ} {A : Type ℓ} = IdS (Id-identity-system {A = A})

-- excellent reduction behaviour

∙ˢ-id-l : (p : x ＝ y) → refl ∙ p ＝ₚ p
∙ˢ-id-l _ = reflₚ

∙ˢ-id-r : (p : x ＝ y) → p ∙ refl ＝ₚ p
∙ˢ-id-r _ = reflₚ

∙ˢ-assoc
  : (p : x ＝ y) (q : y ＝ z) (r : z ＝ w)
  → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
∙ˢ-assoc _ _ _ = refl
