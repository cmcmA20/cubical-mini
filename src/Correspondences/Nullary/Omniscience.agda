{-# OPTIONS --safe #-}
module Correspondences.Nullary.Omniscience where

open import Foundations.Base

open import Meta.Idiom
open import Meta.HLevel

open import Structures.n-Type

open import Correspondences.Nullary.Classical
open import Correspondences.Nullary.Separated
open import Correspondences.Unary.Decidable

open import Data.Dec.Base as Dec
open import Data.Empty.Base
open import Data.Empty.Instances.HLevel

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∥_∥₁; ∣_∣₁)

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
omniscient→exhaustible omn P? = Dec.map
  (λ ¬∃p x → dec→¬¬-stable (P? x) $ ¬∃p ∘ (x ,_))
  (λ ¬∃p ∀p → ¬∃p λ p → p .snd $ ∀p $ p .fst)
  (¬ᵈ omn (¬ᵈ_ ∘ P?))

Exhaustible₁ : Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
Exhaustible₁ {ℓ′} A = {P : Pred₁ ℓ′ A}
                    → Decidable₁ P → Dec (Π[ a ꞉ A ] ⌞ P a ⌟)

Omniscient₁ : Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
Omniscient₁ {ℓ′} A = {P : Pred₁ ℓ′ A}
                   → Decidable₁ P → Dec ∥ Σ[ a ꞉ A ] ⌞ P a ⌟ ∥₁

-- what the hell
omniscient₁→exhaustible₁ : Omniscient₁ {ℓ′ = ℓ′} A → Exhaustible₁ {ℓ′ = ℓ′} A
omniscient₁→exhaustible₁ omn₁ {P} P? = Dec.map
  (λ ¬∃∣p∣₁ x → ∥-∥₁.proj $ dec→¬¬-stable (map pure ∥-∥₁.rec! $ P? x)
    (¬∃∣p∣₁ ∘ λ ¬∣p∣₁ → pure $ x , λ p → ¬∣p∣₁ $ pure p))
  (λ ¬∃∣p∣₁ ∀p → ¬∃∣p∣₁ $ ∥-∥₁.rec! λ x → x .snd $ ∀p $ x .fst)
  (¬ᵈ omn₁ {P = λ x → el! $ ¬ ⌞ P x ⌟} (¬ᵈ_ ∘ P?))
