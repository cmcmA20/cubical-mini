{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Correspondences.Unary.Any.Computational where

open import Meta.Prelude
open import Meta.Effect
open Variadics _

open import Logic.Decidability

open import Data.Dec as Dec
open import Data.Fin.Computational.Base
open import Data.Vec.Inductive.Operations.Computational
open import Data.Sum.Base

private variable
  a a′ : Level
  A : Type a
  P : Pred A a′
  n : ℕ

Any : ∀ {a a′} {n} {A : Type a} (P : Pred A a′) → Vec A n → Type _
Any {n} P xs = Σ[ idx ꞉ Fin n ] P (lookup xs idx)

any? : Decidable P → Decidable (λ (xs : Vec A n) → Any P xs)
any? {n = 0}     P? {([])}       = no λ()
any? {n = suc n} P? {x ∷ xs} =
  Dec.dmap [ (fzero ,_) , bimap fsuc id ]ᵤ
           (_∘ go)
           (P? <+> any? (λ {z} → P? {z}) {xs})
  where
  go : _
  go (mk-fin 0       , p)  = inl p
  go (mk-fin (suc _) , ps) = inr (_ , ps)
