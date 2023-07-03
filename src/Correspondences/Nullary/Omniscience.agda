{-# OPTIONS --safe #-}
module Correspondences.Nullary.Omniscience where

open import Foundations.Base

open import Meta.Idiom
open import Meta.Search.HLevel

open import Structures.n-Type

open import Correspondences.Nullary.Decidable
open import Correspondences.Nullary.Classical
open import Correspondences.Nullary.Separated
open import Correspondences.Unary.Decidable

open import Data.Dec.Base as Dec
open import Data.Empty.Base

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∥_∥₁; ∣_∣₁)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

opaque
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
    (decision-β $ ¬-decision $ decision-η $ omn $
       decision-β ∘ ¬-decision ∘ decision-η ∘ P?)
  -- ^ FIXME what an abomination

  Exhaustible₁ : Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
  Exhaustible₁ {ℓ′} A = {P : Pred₁ ℓ′ A}
                      → Decidable₁ P → Dec (Π[ a ꞉ A ] ⌞ P a ⌟)

  Omniscient₁ : Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
  Omniscient₁ {ℓ′} A = {P : Pred₁ ℓ′ A}
                     → Decidable₁ P → Dec ∥ Σ[ a ꞉ A ] ⌞ P a ⌟ ∥₁

  -- what the hell
  omniscient₁→exhaustible₁ : Omniscient₁ {ℓ′ = ℓ′} A → Exhaustible₁ {ℓ′ = ℓ′} A
  omniscient₁→exhaustible₁ omn₁ {P} P? = Dec.map
    (λ ¬∃∣p∣₁ x → ∥-∥₁.proj! $ dec→¬¬-stable (Dec.map pure ∥-∥₁.rec! $ P? x)
      (¬∃∣p∣₁ ∘ λ ¬∣p∣₁ → pure $ x , λ p → ¬∣p∣₁ $ pure p))
    (λ ¬∃∣p∣₁ ∀p → ¬∃∣p∣₁ $ ∥-∥₁.rec! λ x → x .snd $ ∀p $ x .fst)
      helper where opaque
        unfolding is-of-hlevel n-Type-carrier
        helper : Dec (¬ ∥ Σ[ v ꞉ _ ] (¬ ⌞ P v ⌟) ∥₁)
        helper = decision-β $ ¬-decision $ decision-η $
          omn₁ {P = λ x → (¬ (P x) .fst) , ¬-is-prop} $
            decision-β ∘ ¬-decision ∘ decision-η ∘ P?
