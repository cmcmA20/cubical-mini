{-# OPTIONS --safe #-}
module Data.Id.Properties where

open import Foundations.Prelude
  renaming ( _＝_ to _＝ₚ_
           )

open import Data.Id.Base

private variable
  ℓᵃ : Level
  A : 𝒰 ℓᵃ
  x y z w : A

Id-identity-system : {A : Type ℓᵃ} → is-identity-system (_＝_ {A = A}) (λ _ → refl)
Id-identity-system .to-path p = p _ refl
Id-identity-system .to-path-over f = fun-ext λ _ → fun-ext λ q →
  Jₚ (λ y p → ＜ sym p ／ (λ i → y ＝ₚ f _ reflₚ i) ＼ f _ (sym p) ＞)
     ((λ i j → f _ refl (i ∧ j))) (sym q)

Id≃path : (x ＝ y) ≃ (x ＝ₚ y)
Id≃path = identity-system-gives-path Id-identity-system

module Id≃path {ℓ} {A : Type ℓ} = IdS (Id-identity-system {A = A})

-- excellent reduction behaviour

∙ˢ-id-l : {A : Type ℓᵃ} {x y : A}
        → (p : x ＝ y) → refl ∙ p ＝ₚ p
∙ˢ-id-l _ = refl

∙ˢ-id-r : {A : Type ℓᵃ} {x y : A}
        → (p : x ＝ y) → p ∙ refl ＝ₚ p
∙ˢ-id-r _ = refl

∙ˢ-assoc
  : {A : Type ℓᵃ} {x y z w : A}
    (p : x ＝ y) (q : y ＝ z) (r : z ＝ w)
  → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
∙ˢ-assoc _ _ _ = refl
