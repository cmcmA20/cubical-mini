{-# OPTIONS --safe #-}
module Correspondences.Finite.ManifestBishop where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Discrete
open import Meta.Search.HLevel

open import Correspondences.Omniscient

open import Data.Empty.Base
open import Data.Empty.Instances.HLevel
open import Data.Dec.Base as Dec
open import Data.FinSub.Base
open import Data.FinSub.Instances.Discrete
open import Data.Nat
open import Data.Vec.Base
open import Data.Vec.Operations.Computational
open import Data.Vec.Correspondences.Unary.Any.Computational

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
  unfolding 𝓑 Omniscient₁ Fin lookup vec-fun-equiv
  𝓑→omniscient₁ : 𝓑 A → Omniscient₁ {ℓ′ = ℓ′} A
  𝓑→omniscient₁ {A} (n , aeq) {P} P? =
    Dec.map lemma₁ lemma₂ (any? P? xs) where
      module Ã = Equiv aeq
      module Ṽ = Equiv vec-fun-equiv

      xs : Vec A n
      xs = Ṽ.from $ Ã.from

      lemma₁ : Σ[ i ꞉ Fin n ] P (lookup xs i) → ∥ Σ[ a ꞉ A ] P a ∥₁
      lemma₁ (i , p) = ∣ lookup xs i , p ∣₁

      lemma₂ : ¬ Σ[ i ꞉ Fin n ] P (lookup xs i) → ¬ ∥ Σ[ a ꞉ A ] P a ∥₁
      lemma₂ ¬p = ∥-∥₁.rec! λ (a , pa) → ¬p $ Ã.to a , subst P (sym (happly (Ṽ.ε _) _ ∙ Ã.η a)) pa
