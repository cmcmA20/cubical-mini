{-# OPTIONS --safe #-}
module Correspondences.Omniscient where

open import Foundations.Base

open import Meta.Search.HLevel

open import Structures.n-Type

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
  ℓ ℓ′ : Level
  A : Type ℓ

opaque
  is-omniscient : {ℓ′ : Level} → Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
  is-omniscient {ℓ′} A = {P : Pred₁ ℓ′ A} → Decidable ⌞ P ⌟ₚ → Dec (∃[ a ꞉ A ] ⌞ P a ⌟)

  is-omniscient-β : is-omniscient A → {P : Pred₁ ℓ′ A} → Decidable ⌞ P ⌟ₚ → Dec (∃[ a ꞉ A ] ⌞ P a ⌟)
  is-omniscient-β = id

  is-omniscient-η : ({P : Pred₁ ℓ′ A} → Decidable ⌞ P ⌟ₚ → Dec (∃[ a ꞉ A ] ⌞ P a ⌟)) → is-omniscient A
  is-omniscient-η = id

  is-omniscient-is-prop : is-prop (is-omniscient {ℓ′ = ℓ′} A)
  is-omniscient-is-prop = hlevel!


opaque
  unfolding is-omniscient is-exhaustible Essentially-classical n-Type-carrier
  is-omniscient→is-exhaustible : is-omniscient {ℓ′ = ℓ′} A → is-exhaustible A
  is-omniscient→is-exhaustible omn {P} P? = Dec.map
    (λ ¬∃p x → dec→essentially-classical (P? x) $ ¬∃p ∘ ∣_∣₁ ∘ (x ,_))
    (λ ¬∃p ∀p → ¬∃p $ ∥-∥₁.rec! λ p → p .snd (∀p (p .fst)))
    (¬-decision $ (omn {λ x → el! (¬ (P x .fst))}) $ ¬-decision ∘ P?)

omni : ⦃ x : is-omniscient {ℓ′ = ℓ′} A ⦄ → is-omniscient A
omni ⦃ x ⦄ = x
