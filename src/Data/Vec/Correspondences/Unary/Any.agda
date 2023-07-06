{-# OPTIONS --safe #-}
module Data.Vec.Correspondences.Unary.Any where

open import Foundations.Base

open import Meta.Search.Decidable

open import Correspondences.Decidable

import      Data.Dec as Dec
open Dec
open import Data.Fin.Base
open import Data.Vec.Operations
open import Data.Sum.Base
open import Data.Sum.Instances.Decidable

private variable
  a a′ : Level
  A : Type a
  P : Pred a′ A

Any : ∀ {a a′} {n} {A : Type a} (P : Pred a′ A) → Vec A n → Type _
Any {n} P xs = Σ[ idx ꞉ Fin n ] P (lookup xs idx)

opaque
  unfolding Decidable is-decidable-at-hlevel
  any? : {n : ℕ} → Decidable P → Decidable (λ xs → Any {n = n} P xs)
  any? {n = 0}     P? [] = no λ()
  any? {n = suc n} P? (x ∷ xs) =
    Dec.map [ (fzero ,_) , (λ { (i , q) → fsuc i , q }) ]ᵤ
            (λ { ¬ps (fzero  , p ) → ¬ps (inl p)
               ; ¬ps (fsuc i , ps) → ¬ps (inr (_ , ps)) })
            (⊎-decision (P? x) (any? P? xs))

-- TODO
-- any-ap
--   : (P : Pred a′ A) (Q : Pred b′ B)
--     {f : A → B} (f′ : ∀{x} → P x → Q (f x))
--     {n : ℕ} (@0 xs : Vec A n) → Any P xs → Any Q (Vec.map f xs)
-- any-ap P Q f′ {n = suc _} (_ ∷ _)  (here  p)  = here (f′ p)
-- any-ap P Q f′ {n = suc _} (_ ∷ xs) (there ps) = there (any-ap P Q f′ xs ps)
