{-# OPTIONS --safe #-}
module Correspondences.Finite.ManifestBishop where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Decidable
open import Meta.Search.HLevel

open import Correspondences.Decidable
open import Correspondences.Omniscient

open import Data.Empty.Base
open import Data.Dec.Base as Dec
open import Data.Fin.Base
open import Data.Fin.Instances.Decidable
open import Data.Nat
open import Data.Vec.Base
open import Data.Vec.Operations
open import Data.Vec.Properties
open import Data.Vec.Correspondences.Unary.Any

open import Truncation.Propositional as ∥-∥₁

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

opaque
  𝓑 : Type ℓ → Type ℓ
  𝓑 A = Σ[ n ꞉ ℕ ] (A ≃ Fin n)

  𝓑-is-set : is-set (𝓑 A)
  𝓑-is-set = hlevel!

opaque
  unfolding 𝓑 is-omniscient-at-hlevel is-decidable-at-hlevel any?
  𝓑→is-omniscient : 𝓑 A → is-omniscient {ℓ′ = ℓ′} A
  𝓑→is-omniscient {A} (n , aeq) {P} P? =
    Dec.map lemma₁ lemma₂ (any? P? xs) where
      module Ã = Equiv aeq
      module Ṽ = Equiv vec-fun-equiv

      xs : Vec A n
      xs = Ṽ.inverse .fst $ Ã.inverse .fst

      lemma₁ : _
      lemma₁ (i , p) = ∣ lookup xs i , p ∣₁

      lemma₂ : _
      lemma₂ ¬p = ∥-∥₁.rec! λ (a , pa) → ¬p $ Ã.to a , subst ⌞ P ⌟ₚ (sym (happly (Ṽ.ε _) _ ∙ Ã.η a)) pa
