{-# OPTIONS --safe #-}
module Data.Truncation.Set.Properties where

open import Meta.Prelude

open import Data.Truncation.Set.Base

private variable
  ℓ ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ

∥-∥₂-idempotent : is-set A → is-equiv ∣_∣₂
∥-∥₂-idempotent {A} A-set = is-inv→is-equiv $ invertible proj! (fun-ext inc∘proj) refl where
  instance _ = hlevel-basic-instance 2 A-set
           _ = hlevel-basic-instance 2 squash₂
  inc∘proj : (x : ∥ A ∥₂) → ∣ proj! x ∣₂ ＝ x
  inc∘proj = elim! λ _ → refl

universal : is-set B → (∥ A ∥₂ → B) ≃ (A → B)
universal {B} {A} B-set = ≅→≃ $ iso ff gg refl (fun-ext li) where
  instance _ = hlevel-basic-instance 2 B-set
  ff : (∥ A ∥₂ → B) → A → B
  ff f t = f ∣ t ∣₂

  gg : (A → B) → ∥ A ∥₂ → B
  gg = rec!

  li : gg retract-of′ ff
  li f = fun-ext (elim! λ _ → refl)

is-set→equiv-∥-∥₂ : is-set A → A ≃ ∥ A ∥₂
is-set→equiv-∥-∥₂ A-set = ≅→≃ $ iso ∣_∣₂ proj! (fun-ext $ elim! λ _ → refl) refl where
  instance _ = hlevel-basic-instance 2 A-set
           _ = hlevel-basic-instance 2 squash₂
