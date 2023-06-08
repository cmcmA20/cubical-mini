{-# OPTIONS --safe #-}
module Structures.Omniscience where

open import Foundations.Base
open import Data.Dec.Base

open import Structures.DoubleNegation

open import Correspondences.Unary.Decidable

import Truncation.Propositional.Base as ∥-∥₁
open ∥-∥₁ using (∥_∥₁)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

Exhaustible : Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
Exhaustible {ℓ′} A = {P : Pred ℓ′ A}
                   → Decidable P → Dec (Π[ a ꞉ A ] P a)

Omniscient : Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
Omniscient {ℓ′} A = {P : Pred ℓ′ A}
                  → Decidable P → Dec (Σ[ a ꞉ A ] P a)

omniscient→exhaustible : Omniscient {ℓ′ = ℓ′} A → Exhaustible {ℓ′ = ℓ′} A
omniscient→exhaustible omn P? = map
  (λ ¬∃p x → dec→¬¬-stable (P? x) (¬∃p ∘ (x ,_)))
  (λ ¬∃p ∀p → ¬∃p λ p → p .snd (∀p (p .fst)))
  (¬ᵈ omn (¬ᵈ_ ∘ P?))

Omniscient₁ : Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
Omniscient₁ {ℓ′} A = {P : Pred ℓ′ A}
                   → Decidable P → Dec ∥ Σ[ a ꞉ A ] P a ∥₁
