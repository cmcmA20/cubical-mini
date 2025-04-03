{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Membership where

open import Foundations.Base

open import Meta.Effect.Alternative

open import Logic.Discreteness

open import Data.Dec as Dec
open import Data.Empty.Base
open import Data.Fin.Inductive.Base
open import Data.Sum.Base
open import Data.Vec.Inductive.Operations

open Alternative ⦃ ... ⦄

private variable
  ℓ : Level
  A : Type ℓ
  @0 n : ℕ

_∈ᵥ_ : A → Vec A n → Type _
x ∈ᵥ xs = Σ[ idx ꞉ Fin _ ] (lookup xs idx ＝ x)

hereᵥ : ∀ {x y} {xs : Vec A n} → x ＝ y → x ∈ᵥ (y ∷ xs)
hereᵥ e = fzero , e ⁻¹

thereᵥ : ∀ {x y} {xs : Vec A n} → x ∈ᵥ xs → x ∈ᵥ (y ∷ xs)
thereᵥ (idx , e) = fsuc idx , e

∈ᵥ-uncons : ∀ {z : A} {x} {xs : Vec A n}
          → z ∈ᵥ (x ∷ xs) → (z ＝ x) ⊎ z ∈ᵥ xs
∈ᵥ-uncons               (fzero    , e) = inl (e ⁻¹)
∈ᵥ-uncons {xs = y ∷ xs} (fsuc idx , e) =
  inr $ [ hereᵥ , thereᵥ ]ᵤ (∈ᵥ-uncons {xs = xs} (idx , e))

instance
  Membership-Vec : Membership A (Vec A n) (level-of-type A)
  Membership-Vec ._∈_ = _∈ᵥ_

instance
  Dec-∈ᵥ : ⦃ di : is-discrete A ⦄
         → {x : A} {as : Vec A n} → Dec (x ∈ as)
  Dec-∈ᵥ {n = 0} {x} {([])} = no λ()
  Dec-∈ᵥ {n = suc _} {x} {a ∷ as} =
    Dec.dmap [ fzero ,_ , bimap fsuc id ]ᵤ
             (contra go)
             (a ≟ x <+> Dec-∈ᵥ {x = x} {as})
    where
    go : _
    go (fzero  , q) = inl q
    go (fsuc k , q) = inr (_ , q)
  {-# INCOHERENT Dec-∈ᵥ #-} -- really?
