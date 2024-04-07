{-# OPTIONS --safe #-}
module Truncation.Set.Base where

open import Meta.Prelude

data ∥_∥₂ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₂    : A → ∥ A ∥₂
  squash₂ : (x y : ∥ A ∥₂) (p q : x ＝ y) → p ＝ q

private variable
  ℓ ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ

instance opaque
  H-Level-∥-∥₂ : ∀ {n} → H-Level (2 + n) ∥ A ∥₂
  H-Level-∥-∥₂ = hlevel-basic-instance 2 squash₂

elim : {A : Type ℓᵃ} {P : ∥ A ∥₂ → Type ℓ}
     → Π[ x ꞉ ∥ A ∥₂ ] is-set (P x)
     → Π[ x ꞉   A    ] P ∣ x ∣₂
     → Π[ x ꞉ ∥ A ∥₂ ] P   x
elim _ incc ∣ x ∣₂ = incc x
elim P-set incc (squash₂ x y p q i j) =
  is-set→squareᴾ (λ k l → P-set (squash₂ x y p q k l))
    (λ _ → go x) (λ k → go (p k)) (λ k → go (q k)) (λ _ → go y) i j
    where go = elim P-set incc

elim² : {C : ∥ A ∥₂ → ∥ B ∥₂ → Type ℓ}
      → (∀ x y → is-set (C x y))
      → (∀ x y → C ∣ x ∣₂ ∣ y ∣₂)
      → ∀ x y → C x y
elim² B-set f = elim (λ x → Π-is-of-hlevel 2 (B-set x))
  λ x → elim (B-set ∣ x ∣₂) (f x)

elim³ : {D : ∥ A ∥₂ → ∥ B ∥₂ → ∥ C ∥₂ → Type ℓ}
      → (∀ x y z → is-set (D x y z))
      → (∀ x y z → D ∣ x ∣₂ ∣ y ∣₂ ∣ z ∣₂)
      → ∀ x y z → D x y z
elim³ B-set f = elim² (λ x y → Π-is-of-hlevel 2 (B-set x y))
  λ x y → elim (B-set ∣ x ∣₂ ∣ y ∣₂) (f x y)

rec : is-set B → (A → B) → ∥ A ∥₂ → B
rec _ f ∣ x ∣₂ = f x
rec B-set f (squash₂ x y p q i j) =
  B-set (go x) (go y) (λ k → go (p k)) (λ k → go (q k)) i j where
    go = rec B-set f

rec² : is-set C → (A → B → C) → ∥ A ∥₂ → ∥ B ∥₂ → C
rec² C-set = elim² (λ _ _ → C-set)

proj : (A-set : is-set A) → ∥ A ∥₂ → A
proj A-set = rec A-set id


-- Automation

elim!
  : {A : Type ℓᵃ} {P : ∥ A ∥₂ → Type ℓ}
    ⦃ P-set : ∀{a} → H-Level 2 (P a) ⦄
  → Π[ a ꞉ A ] P ∣ a ∣₂
  → (x : ∥ A ∥₂) → P x
elim! = elim λ _ → hlevel 2

elim!² : {C : ∥ A ∥₂ → ∥ B ∥₂ → Type ℓ}
       → ⦃ C-set : ∀ {x y} → H-Level 2 (C x y) ⦄
       → (∀ x y → C ∣ x ∣₂ ∣ y ∣₂)
       → ∀ x y → C x y
elim!² = elim² (λ _ _ → hlevel 2)

rec!
  : ⦃ B-set : H-Level 2 B ⦄
  → (A → B)
  → (x : ∥ A ∥₂) → B
rec! = rec (hlevel 2)

proj!
  : ⦃ A-set : H-Level 2 A ⦄
  → ∥ A ∥₂ → A
proj! = rec! id
