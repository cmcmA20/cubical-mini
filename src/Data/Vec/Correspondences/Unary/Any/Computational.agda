{-# OPTIONS --safe #-}
module Data.Vec.Correspondences.Unary.Any.Computational where

open import Foundations.Base

open import Meta.Search.Decidable

open import Correspondences.Decidable

import      Data.Dec as Dec
open Dec
open import Data.FinSub.Base
open import Data.Vec.Operations.Computational
open import Data.Sum.Base
open import Data.Sum.Instances.Decidable

private variable
  a a′ : Level
  A : Type a
  P : Pred a′ A

Any : ∀ {a a′} {n} {A : Type a} (P : Pred a′ A) → Vec A n → Type _
Any {n} P xs = Σ[ idx ꞉ Fin n ] P (lookup xs idx)

opaque
  unfolding Fin lookup
  any? : {n : ℕ} → Decidable P → Decidable (λ xs → Any {n = n} P xs)
  any? {n = 0}     P? [] = no λ()
  any? {n = suc n} P? (x ∷ xs) =
    Dec.map [ (fzero ,_) , (λ { (i , q) → fsuc i , q }) ]ᵤ
            (λ { ¬ps ((0 , _)  , p ) → ¬ps (inl p)
               ; ¬ps ((suc i , _) , ps) → ¬ps (inr (_ , ps)) })
            (⊎-decision (P? x) (any? P? xs))
