{-# OPTIONS --safe #-}
module Truncation.Set.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Truncation.Set.Base public

private variable
  ℓ ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ

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

rec!
  : {@(tactic hlevel-tactic-worker) B-set : is-set B}
  → (A → B)
  → (x : ∥ A ∥₂) → B
rec! {B-set} = elim (λ _ → B-set)

elim!
  : {P : ∥ A ∥₂ → Type ℓ}
    {@(tactic hlevel-tactic-worker) P-set : ∀{a} → is-set (P a)}
  → Π[ a ꞉ A ] P ∣ a ∣₂
  → (x : ∥ A ∥₂) → P x
elim! {P-set} = elim (λ _ → P-set)

proj!
  : {@(tactic hlevel-tactic-worker) A-set : is-set A}
  → ∥ A ∥₂ → A
proj! {A-set} = rec A-set id

∥-∥₂-idempotent : is-set A → is-equiv ∣_∣₂
∥-∥₂-idempotent {A} A-set = is-iso→is-equiv $ iso (proj A-set) inc∘proj λ _ → refl where
  inc∘proj : (x : ∥ A ∥₂) → ∣ proj A-set x ∣₂ ＝ x
  inc∘proj = elim! λ _ → refl

universal : is-set B → (∥ A ∥₂ → B) ≃ (A → B)
universal {B} {A} B-set = iso→≃ (ff , iso  gg (λ _ → refl) li) where
  instance _ = hlevel-basic-instance 2 B-set
  ff : (∥ A ∥₂ → B) → A → B
  ff f t = f ∣ t ∣₂

  gg : (A → B) → ∥ A ∥₂ → B
  gg = rec!

  li : gg is-left-inverse-of ff
  li f = fun-ext (elim! λ _ → refl)

is-set→equiv-∥-∥₂ : is-set A → A ≃ ∥ A ∥₂
is-set→equiv-∥-∥₂ A-set = iso→≃ $ ∣_∣₂ , iso proj! (elim! λ _ → refl) λ _ → refl where
  instance _ = hlevel-basic-instance 2 A-set
