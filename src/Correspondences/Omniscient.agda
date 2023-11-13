{-# OPTIONS --safe #-}
module Correspondences.Omniscient where

open import Foundations.Base

open import Meta.Search.HLevel

open import Correspondences.Base public
open import Correspondences.Classical
open import Correspondences.Decidable
open import Correspondences.Exhaustible

open import Data.Dec as Dec
import Data.Empty.Base as ⊥
open ⊥ using (¬_)

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∥_∥₁; ∣_∣₁; ∃-syntax)

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ

record Omniscient₁ {ℓ : Level} (A : Type ℓᵃ) : Type (ℓᵃ ⊔ ℓsuc ℓ) where
  no-eta-equality
  constructor omniscient₁-η
  field omniscient₁-β : {P : Pred ℓ A} → Decidable¹ P → Dec (∃[ a ꞉ A ] P a)

open Omniscient₁ public

omniscient₁→exhaustible : Omniscient₁ {ℓ = ℓ} A → Exhaustible {ℓ = ℓ} A
omniscient₁→exhaustible omn .exhaustible-β {P} P? = Dec.map
  (λ ¬∃p x → dec→essentially-classical (P? x) $ ¬∃p ∘ ∣_∣₁ ∘ (x ,_))
  (λ ¬∃p ∀p → ¬∃p $ ∥-∥₁.rec! λ p → p .snd (∀p (p .fst)))
  (¬-decision $ omn .omniscient₁-β (¬-decision ∘ P?))

omni₁ : ⦃ x : Omniscient₁ {ℓ = ℓ} A ⦄ → Omniscient₁ A
omni₁ ⦃ x ⦄ = x

∃-decision : {B : A → Type ℓᵇ} → Decidable¹ B → Omniscient₁ A → Dec (∃[ a ꞉ A ] B a)
∃-decision d ex = omniscient₁-β ex d
