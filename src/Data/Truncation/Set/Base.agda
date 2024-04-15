{-# OPTIONS --safe #-}
module Data.Truncation.Set.Base where

open import Meta.Prelude

data ∥_∥₂ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₂    : A → ∥ A ∥₂
  squash₂ : is-set ∥ A ∥₂

private variable
  ℓ ℓᵃ : Level
  A : Type ℓᵃ

elim : {A : Type ℓᵃ} {P : ∥ A ∥₂ → Type ℓ}
     → Π[ x ꞉ ∥ A ∥₂ ] is-set (P x)
     → Π[ x ꞉   A    ] P ∣ x ∣₂
     → Π[ x ꞉ ∥ A ∥₂ ] P   x
elim _ incc ∣ x ∣₂ = incc x
elim P-set incc (squash₂ x y p q i j) =
  is-set→squareᴾ (λ k l → P-set (squash₂ x y p q k l))
    (λ _ → go x) (λ k → go (p k)) (λ k → go (q k)) (λ _ → go y) i j
    where go = elim P-set incc


-- Automation

instance opaque
  H-Level-∥-∥₂ : ∀ {n} → H-Level (2 + n) ∥ A ∥₂
  H-Level-∥-∥₂ = hlevel-basic-instance 2 squash₂

instance
  Inductive-∥-∥₂
    : ∀ {ℓ ℓ′ ℓm} {A : Type ℓ} {P : ∥ A ∥₂ → Type ℓ′}
      ⦃ i : Inductive (∀ x → P ∣ x ∣₂) ℓm ⦄
    → ⦃ pr : ∀ {x} → H-Level 2 (P x) ⦄
    → Inductive (∀ x → P x) ℓm
  Inductive-∥-∥₂ ⦃ i ⦄ .Inductive.methods = i .Inductive.methods
  Inductive-∥-∥₂ ⦃ i ⦄ .Inductive.from f = elim hlevel! (i .Inductive.from f)

proj!
  : ⦃ A-set : H-Level 2 A ⦄
  → ∥ A ∥₂ → A
proj! = rec! id
