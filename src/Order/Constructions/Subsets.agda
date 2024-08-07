{-# OPTIONS --safe #-}
module Order.Constructions.Subsets where

open import Categories.Prelude
open import Order.Base
open import Order.Constructions.Props
open import Order.Constructions.Pointwise
open import Order.Diagram.Join
import Order.Reasoning

private variable o ℓ o′ ℓ′ ℓᵢ : Level

@0 Subsets : ∀ {ℓˣ} (X : Type ℓˣ) (ℓ : Level) → Poset (ℓˣ ⊔ ℓsuc ℓ) (ℓˣ ⊔ ℓ)
Subsets X ℓ = Pointwise X (λ _ → Props ℓ)

ℙ-ctramap
  : ∀{ℓ ℓˣ ℓʸ} {X : Type ℓˣ} {Y : Type ℓʸ}
  → (f : Y → X) → Subsets X ℓ ⇒ Subsets Y ℓ
ℙ-ctramap f .hom A = A ∘ₜ f
ℙ-ctramap _ .pres-≤ z = z

ℙ-map
  : ∀{ℓ ℓˣ ℓʸ} {X : Type ℓˣ} {Y : Type ℓʸ}
  → (f : X → Y) → Subsets X ℓ ⇒ Subsets Y (ℓˣ ⊔ ℓʸ ⊔ ℓ)
ℙ-map {X} f .hom A y = el! (∃[ x ꞉ X ] (f x ＝ y) × (x ∈ A))
ℙ-map f .pres-≤ z = map (second (second z))
