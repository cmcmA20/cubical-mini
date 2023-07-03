{-# OPTIONS --safe #-}
module Truncation.Set.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Truncation.Set.Base public

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″

map₂ : (A → B → C) → ∥ A ∥₂ → ∥ B ∥₂ → ∥ C ∥₂
map₂ f ∣ x ∣₂ ∣ y ∣₂ = ∣ f x y ∣₂
map₂ f (squash₂ x y p q i j) b =
  squash₂ (map₂ f x b) (map₂ f y b)
          (λ k → map₂ f (p k) b)
          (λ k → map₂ f (q k) b)
          i j
map₂ f a (squash₂ x y p q i j) =
  squash₂ (map₂ f a x) (map₂ f a y)
          (λ k → map₂ f a (p k))
          (λ k → map₂ f a (q k))
          i j

elim₂ : {C : ∥ A ∥₂ → ∥ B ∥₂ → Type ℓ″}
      → (∀ x y → is-set (C x y))
      → (∀ x y → C ∣ x ∣₂ ∣ y ∣₂)
      → ∀ x y → C x y
elim₂ B-set f = elim (λ x → Π-is-of-hlevel 2 (B-set x))
  λ x → elim (B-set ∣ x ∣₂) (f x)

elim₃ : {D : ∥ A ∥₂ → ∥ B ∥₂ → ∥ C ∥₂ → Type ℓ‴}
      → (∀ x y z → is-set (D x y z))
      → (∀ x y z → D ∣ x ∣₂ ∣ y ∣₂ ∣ z ∣₂)
      → ∀ x y z → D x y z
elim₃ B-set f = elim₂ (λ x y → Π-is-of-hlevel 2 (B-set x y))
  λ x y → elim (B-set ∣ x ∣₂ ∣ y ∣₂) (f x y)

rec!
  : {@(tactic hlevel-tactic-worker) B-set : is-set B}
  → (A → B)
  → (x : ∥ A ∥₂) → B
rec! {B-set} = elim (λ _ → B-set)

elim!
  : {P : ∥ A ∥₂ → Type ℓ′}
    {@(tactic hlevel-tactic-worker) P-set : ∀{a} → is-set (P a)}
  → Π[ a ꞉ A ] P ∣ a ∣₂
  → (x : ∥ A ∥₂) → P x
elim! {P-set} = elim (λ _ → P-set)

proj!
  : {@(tactic hlevel-tactic-worker) A-set : is-set A}
  → ∥ A ∥₂ → A
proj! {A-set} = rec A-set id

opaque
  unfolding rec
  ∥-∥₂-idempotent : is-set A → is-equiv ∣_∣₂
  ∥-∥₂-idempotent {A} A-set = is-iso→is-equiv $ iso (proj A-set) inc∘proj λ _ → refl where
    inc∘proj : (x : ∥ A ∥₂) → ∣ proj A-set x ∣₂ ＝ x
    inc∘proj = elim (λ _ → is-prop→is-set (squash₂ _ _)) λ _ → refl
