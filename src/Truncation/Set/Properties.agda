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
