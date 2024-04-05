{-# OPTIONS --safe #-}
module Truncation.Set.Properties where

open import Meta.Prelude

open import Structures.n-Type

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
  : ⦃ B-set : H-Level 2 B ⦄
  → (A → B)
  → (x : ∥ A ∥₂) → B
rec! = elim hlevel!

elim!
  : {A : Type ℓᵃ} {P : ∥ A ∥₂ → Type ℓ}
    ⦃ P-set : ∀{a} → H-Level 2 (P a) ⦄
  → Π[ a ꞉ A ] P ∣ a ∣₂
  → (x : ∥ A ∥₂) → P x
elim! = elim hlevel!

proj!
  : ⦃ A-set : H-Level 2 A ⦄
  → ∥ A ∥₂ → A
proj! = rec! id

∥-∥₂-idempotent : is-set A → is-equiv ∣_∣₂
∥-∥₂-idempotent {A} A-set = is-iso→is-equiv $ iso (proj A-set) inc∘proj λ _ → refl where
  inc∘proj : (x : ∥ A ∥₂) → ∣ proj A-set x ∣₂ ＝ x
  inc∘proj = elim! λ _ → refl

universal : is-set B → (∥ A ∥₂ → B) ≃ (A → B)
universal {B} {A} B-set = ≅→≃ (ff , iso  gg (λ _ → refl) li) where
  instance _ = hlevel-basic-instance 2 B-set
  ff : (∥ A ∥₂ → B) → A → B
  ff f t = f ∣ t ∣₂

  gg : (A → B) → ∥ A ∥₂ → B
  gg = rec!

  li : gg is-left-inverse-of ff
  li f = fun-ext (elim! λ _ → refl)

is-set→equiv-∥-∥₂ : is-set A → A ≃ ∥ A ∥₂
is-set→equiv-∥-∥₂ A-set = ≅→≃ $ ∣_∣₂ , iso proj! (elim! λ _ → refl) λ _ → refl where
  instance _ = hlevel-basic-instance 2 A-set
