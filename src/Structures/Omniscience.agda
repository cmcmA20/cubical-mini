{-# OPTIONS --safe #-}
module Structures.Omniscience where

open import Foundations.Base
open import Data.Dec.Base public

open import Structures.DoubleNegation

open import Correspondences.Unary.Decidable

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

Exhaustible : Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
Exhaustible {ℓ′} A = {P : A → Type ℓ′}
                   → Decidable P → Dec (Π[ a ꞉ A ] (P a))

Omniscient : Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
Omniscient {ℓ′} A = {P : A → Type ℓ′}
                  → Decidable P → Dec (Σ[ a ꞉ A ] (P a))

omniscient→exhaustible : Omniscient {ℓ′ = ℓ′} A → Exhaustible {ℓ′ = ℓ′} A
omniscient→exhaustible omn P? = map
  (λ ¬∃p x → dec→¬¬-stable (P? x) (¬∃p ∘ (x ,_)))
  (λ ¬∃p ∀p → ¬∃p λ p → p .snd (∀p (p .fst)))
  (¬ᵈ omn (¬ᵈ_ ∘ P?))
