{-# OPTIONS --safe #-}
module Correspondences.Nullary.Finite.ManifestBishop where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Correspondences.Nullary.Decidable
open import Correspondences.Nullary.Omniscience

open import Data.Dec.Base as Dec
open import Data.Fin.Base
open import Data.Fin.Instances.Discrete
open import Data.Nat
open import Data.Vec.Base
open import Data.Vec.Properties
open import Data.Vec.Correspondences.Unary.Any

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

opaque
  𝓑 : Type ℓ → Type ℓ
  𝓑 A = Σ[ n ꞉ ℕ ] (A ≃ Fin n)

  𝓑-is-set : is-set (𝓑 A)
  𝓑-is-set = hlevel!

opaque
  unfolding 𝓑 Omniscient
  𝓑→omniscient : 𝓑 A → Omniscient {ℓ′ = ℓ′} A
  𝓑→omniscient {A} (n , aeq) {P} P? =
    Dec.map lemma₁ lemma₂ (any? P? xs) where
      module Ã = Equiv aeq
      module Ṽ = Equiv vec-fun-equiv

      xs : Vec A n
      xs = Ṽ.inverse .fst $ Ã.inverse .fst

      lemma₁ : _
      lemma₁ (i , p) = lookup xs i , p

      lemma₂ : _
      lemma₂ ¬p (a , pa) = ¬p $ Ã.to a , subst P (sym (happly (Ṽ.ε _) _ ∙ Ã.η a)) pa
