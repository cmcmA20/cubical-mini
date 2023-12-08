{-# OPTIONS --safe #-}
module Correspondences.Omniscient where

open import Foundations.Base

open import Meta.Effect.Map
open import Meta.Search.HLevel
open import Meta.Variadic

open import Correspondences.Base public
open import Correspondences.Classical
open import Correspondences.Decidable
open import Correspondences.Exhaustible

open import Data.Dec as Dec
open import Data.Empty.Base as ⊥
  using (¬_)

open import Truncation.Propositional as ∥-∥₁
  using (∥_∥₁; ∣_∣₁; ∃-syntax; ∃[_])

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ

record Omniscient₁ {ℓ : Level} {ℓᵃ : Level} (A : Type ℓᵃ) : Type (ℓᵃ ⊔ ℓsuc ℓ) where
  no-eta-equality
  constructor omniscient₁-η
  field omniscient₁-β : {P : Pred A ℓ} → Decidable P → Dec ∃[ P ]

open Omniscient₁ public

omniscient₁→exhaustible : Omniscient₁ {ℓ} A → Exhaustible {ℓ} A
omniscient₁→exhaustible omn .exhaustible-β {P} P? = Dec.dmap
  (λ ¬∃p x → dec→essentially-classical (P? x) $ ¬∃p ∘ ∣_∣₁ ∘ (x ,_))
  (λ ¬∃p ∀p → ¬∃p $ ∥-∥₁.rec! λ p → p .snd (∀p (p .fst)))
  (¬-decision $ omn .omniscient₁-β (¬-decision ∘ P?))

omni₁ : ⦃ x : Omniscient₁ {ℓ} A ⦄ → Omniscient₁ A
omni₁ ⦃ x ⦄ = x

lift-omniscient₁ : Omniscient₁ {ℓ} A → Omniscient₁ (Lift ℓ A)
lift-omniscient₁ omn .omniscient₁-β P? = Dec.dmap
  (map (bimap lift id))
  (λ x y → ∥-∥₁.rec! (λ z → x ∣ bimap lower id z ∣₁) y)
  (omn .omniscient₁-β $ P? ∘ lift)

∃-decision : {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ} {B : Pred A ℓᵇ} → Decidable B → Omniscient₁ A → Dec ∃[ B ]
∃-decision d ex = omniscient₁-β ex d


record Omniscient {ℓ : Level} {ℓᵃ : Level} (A : Type ℓᵃ) : Type (ℓᵃ ⊔ ℓsuc ℓ) where
  no-eta-equality
  constructor omniscient-η
  field omniscient-β : {P : Pred A ℓ} → Decidable P → Dec Σ[ P ]

open Omniscient public

omniscient→omniscient₁ : Omniscient {ℓ} A → Omniscient₁ {ℓ} A
omniscient→omniscient₁ omn .omniscient₁-β d = Dec.dmap
  ∣_∣₁
  ∥-∥₁.rec!
  (omniscient-β omn d)

omni : ⦃ x : Omniscient {ℓ} A ⦄ → Omniscient A
omni ⦃ x ⦄ = x

lift-omniscient : Omniscient {ℓ} A → Omniscient {ℓ} (Lift ℓ A)
lift-omniscient omn .omniscient-β P? = Dec.dmap
  (bimap lift id)
  (_∘ bimap lower id)
  (omn .omniscient-β $ P? ∘ lift)

Σ-decision : {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ} {B : Pred A ℓᵇ} → Decidable B → Omniscient A → Dec Σ[ B ]
Σ-decision d ex = omniscient-β ex d
