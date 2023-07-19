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
open import Data.Empty.Instances.HLevel

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∥_∥₁; ∣_∣₁; ∃-syntax)

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ

opaque
  Omniscient₁ : {ℓ′ : Level} → Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
  Omniscient₁ {ℓ′} A = {P : Pred ℓ′ A} → Decidable P → Dec (∃[ a ꞉ A ] P a)

  omniscient₁-β : Omniscient₁ A → {P : Pred ℓ′ A} → Decidable P → Dec (∃[ a ꞉ A ] P a)
  omniscient₁-β = id

  omniscient₁-η : ({P : Pred ℓ′ A} → Decidable P → Dec (∃[ a ꞉ A ] P a)) → Omniscient₁ A
  omniscient₁-η = id


opaque
  unfolding Omniscient₁ Exhaustible Essentially-classical
  omniscient₁→exhaustible : Omniscient₁ {ℓ′ = ℓ′} A → Exhaustible A
  omniscient₁→exhaustible omn {P} P? = Dec.map
    (λ ¬∃p x → dec→essentially-classical (P? x) $ ¬∃p ∘ ∣_∣₁ ∘ (x ,_))
    (λ ¬∃p ∀p → ¬∃p $ ∥-∥₁.rec! λ p → p .snd (∀p (p .fst)))
    (¬-decision $ omn $ ¬-decision ∘ P?)

omni₁ : ⦃ x : Omniscient₁ {ℓ′ = ℓ′} A ⦄ → Omniscient₁ A
omni₁ ⦃ x ⦄ = x

∃-decision : {B : A → Type ℓᵇ} → Decidable B → Omniscient₁ {ℓ′ = ℓᵇ} A → Dec (∃[ a ꞉ A ] B a)
∃-decision d ex = omniscient₁-β ex d
