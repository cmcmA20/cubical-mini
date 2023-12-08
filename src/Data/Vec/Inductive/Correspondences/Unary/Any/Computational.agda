{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Correspondences.Unary.Any.Computational where

open import Foundations.Base

open import Meta.Search.Decidable
open import Meta.Variadic

open import Correspondences.Decidable

open import Data.Dec as Dec
open import Data.Fin.Computational.Base
open import Data.Vec.Inductive.Operations.Computational
open import Data.Sum.Base
open import Data.Sum.Instances.Decidable

private variable
  a a′ : Level
  A : Type a
  P : Pred A a′
  n : ℕ

Any : ∀ {a a′} {n} {A : Type a} (P : Pred A a′) → Vec A n → Type _
Any {n} P xs = Σ[ idx ꞉ Fin n ] P (lookup xs idx)

any? : Decidable P → Decidable (λ (xs : Vec A n) → Any P xs)
any? {n = 0}     P? []       = no λ()
any? {n = suc n} P? (x ∷ xs) =
  Dec.dmap [ (fzero ,_) , bimap fsuc id ]ᵤ
           go
           (⊎-decision (P? x) (any? P? xs)) where
             go : _
             go ¬ps (mk-fin 0       , p)  = ¬ps (inl p)
             go ¬ps (mk-fin (suc k) , ps) = ¬ps (inr (_ , ps))
