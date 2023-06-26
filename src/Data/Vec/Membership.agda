{-# OPTIONS --safe #-}
module Data.Vec.Membership where

open import Foundations.Base

open import Correspondences.Nullary.Decidable

open import Data.Dec as Dec
open import Data.Empty.Base
open import Data.Fin.Base
open import Data.Sum.Base
open import Data.Vec.Properties

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

_∈_ : A → Vec A n → Type _
x ∈ xs = Σ[ idx ꞉ Fin _ ] (lookup xs idx ＝ x)

_∉_ : A → Vec A n → Type _
x ∉ xs = ¬ (x ∈ xs)

_∈!_ : A → Vec A n → Type _
x ∈! xs = is-contr (x ∈ xs)

_∈?_ : ⦃ is-discrete A ⦄ → Π[ x ꞉ A ] Π[ as ꞉ Vec A n ] Dec (x ∈ as)
_∈?_ {n = 0}     x []       = no λ()
_∈?_ {n = suc _} x (a ∷ as) =
  Dec.map [ fzero ,_ , (λ { (i , q) → fsuc i , q }) ]ᵤ
          (λ { x∉as (fzero  , q) → x∉as $ inl q
             ; x∉as (fsuc i , q) → x∉as $ inr $ i , q })
          (a ≟ x ∨ᵈ x ∈? as)
