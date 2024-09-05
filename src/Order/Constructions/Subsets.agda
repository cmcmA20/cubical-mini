{-# OPTIONS --safe #-}
module Order.Constructions.Subsets where

open import Cat.Prelude
open import Order.Base
open import Order.Constructions.Props
open import Order.Constructions.Pointwise

private variable ℓ ℓˣ ℓʸ : Level

@0 Subsets : (X : Type ℓˣ) (ℓ : Level) → Poset (ℓˣ ⊔ ℓsuc ℓ) (ℓˣ ⊔ ℓ)
Subsets X ℓ = Pointwise X (λ _ → Props ℓ)

ℙ-ctramap
  : {X : Type ℓˣ} {Y : Type ℓʸ}
  → (f : Y → X) → Subsets X ℓ ⇒ Subsets Y ℓ
ℙ-ctramap f .hom A = A ∘ₜ f
ℙ-ctramap _ .pres-≤ z = z

ℙ-map
  : {X : Type ℓˣ} {Y : Type ℓʸ}
  → (f : X → Y) → Subsets X ℓ ⇒ Subsets Y (ℓˣ ⊔ ℓʸ ⊔ ℓ)
ℙ-map {X} f .hom A y = el! (∃[ x ꞉ X ] (f x ＝ y) × (x ∈ A))
ℙ-map f .pres-≤ z = map (second (second z))


module @0 _ {ℓ ℓˣ} {X : Type ℓˣ} where private
  open import Combinatorics.Power.Base
  open import Order.Reasoning (Subsets X ℓ)

  _ : Ob ＝ ℙ X ℓ
  _ = refl

  _ : {A B : Ob} → A ≤ B ＝ A ⊆ B
  _ = refl
