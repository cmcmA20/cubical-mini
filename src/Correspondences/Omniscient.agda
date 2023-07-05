{-# OPTIONS --safe #-}
module Correspondences.Omniscient where

open import Foundations.Base

open import Meta.Idiom
open import Meta.Search.HLevel

open import Structures.n-Type

open import Correspondences.Base public
open import Correspondences.Decidable
open import Correspondences.Exhaustible
open import Correspondences.Separated

import Data.Dec as Dec
import Data.Empty.Base as ⊥
open ⊥ using (¬_)

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∥_∥₁; ∣_∣₁; ∃-syntax)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

opaque
  is-omniscient-at-hlevel : {ℓ′ : Level} → HLevel → Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
  is-omniscient-at-hlevel {ℓ′} 0 A =
    {P : Pred₁ ℓ′ A} → Decidable ⌞ P ⌟ₚ → Decision (∃[ a ꞉ A ] ⌞ P a ⌟)
  is-omniscient-at-hlevel {ℓ′} (suc n) = is-omniscient-at-hlevel {ℓ′ = ℓ′} n on-paths-of_

is-omniscient : {ℓ′ : Level} → Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
is-omniscient {ℓ′} = is-omniscient-at-hlevel {ℓ′ = ℓ′} 0
{-# INLINE is-omniscient #-}

opaque
  unfolding is-omniscient-at-hlevel is-decidable-at-hlevel
  is-omniscient-is-prop : is-prop (is-omniscient {ℓ′ = ℓ′} A)
  is-omniscient-is-prop = hlevel!

  opaque
    unfolding is-exhaustible-at-hlevel Decidable n-Type-carrier
    is-omniscient→is-exhaustible : is-omniscient {ℓ′ = ℓ′} A → is-exhaustible {ℓ′ = ℓ′} A
    is-omniscient→is-exhaustible omn {P} P? = Dec.map
      (λ ¬∃p x → dec→¬¬-stable (P? x) $ ¬∃p ∘ ∣_∣₁ ∘ (x ,_))
      (λ ¬∃p ∀p → ¬∃p $ ∥-∥₁.rec! λ p → p .snd (∀p (p .fst)))
      (¬-decision $ (omn {λ x → el! (¬ (P x .fst))}) $ ¬-decision ∘ P?)
