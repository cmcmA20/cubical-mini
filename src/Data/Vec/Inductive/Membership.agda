{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Membership where

open import Foundations.Base

open import Meta.Membership

open import Logic.Discreteness

open import Data.Dec as Dec
open import Data.Empty.Base
open import Data.Fin.Inductive.Base
open import Data.Sum.Base
open import Data.Sum.Instances.Decidable
open import Data.Vec.Inductive.Operations

private variable
  ℓ : Level
  A : Type ℓ
  @0 n : ℕ

_∈ᵥ_ : A → Vec A n → Type _
x ∈ᵥ xs = Σ[ idx ꞉ Fin _ ] (lookup xs idx ＝ x)

instance
  Membership-Vec : Membership A (Vec A n) (level-of-type A)
  Membership-Vec ._∈_ = _∈ᵥ_

instance
  Dec-∈ᵥ : ⦃ di : is-discrete A ⦄
         → {x : A} {as : Vec A n} → Dec (x ∈ as)
  Dec-∈ᵥ {n = 0} {x} {([])} = no λ()
  Dec-∈ᵥ {n = suc _} {x} {a ∷ as} =
    Dec.dmap [ fzero ,_ , bimap fsuc id ]ᵤ
             (λ { x∉as (fzero  , q) → x∉as $ inl q
                ; x∉as (fsuc i , q) → x∉as $ inr $ i , q })
             (Dec-⊎ ⦃ a ≟ x ⦄ ⦃ Dec-∈ᵥ {x = x} {as} ⦄)
  {-# INCOHERENT Dec-∈ᵥ #-} -- really?
