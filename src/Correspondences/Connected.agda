{-# OPTIONS --safe #-}
module Correspondences.Connected where

open import Foundations.Base

open import Meta.Search.HLevel

open import Correspondences.Base public

open import Truncation.Propositional

private variable
  ℓ : Level
  A : Type ℓ

opaque
  -- weak form of contractibility
  is-connected : Type ℓ → Type ℓ
  is-connected A = ∥ A ∥₁ × (∥_∥₁ on-paths-of A)

  centre₁ : is-connected A → ∥ A ∥₁
  centre₁ = fst

  paths₁ : is-connected A → ∥_∥₁ on-paths-of A
  paths₁ = snd

  is-connected-β : is-connected A → ∥ A ∥₁ × (∥_∥₁ on-paths-of A)
  is-connected-β = id

  is-connected-η : ∥ A ∥₁ × (∥_∥₁ on-paths-of A) → is-connected A
  is-connected-η = id

  instance
    is-connected-is-prop : is-prop (is-connected A)
    is-connected-is-prop = is-prop-η λ _ _ → prop!

is-connected-is-of-hlevel : (n : HLevel) → is-of-hlevel (suc n) (is-connected A)
is-connected-is-of-hlevel n = is-of-hlevel-+-left 1 n is-connected-is-prop

instance
  decomp-hlevel-conn : goal-decomposition (quote is-of-hlevel) (is-connected A)
  decomp-hlevel-conn = decomp (quote is-connected-is-of-hlevel) (`level-minus 1 ∷ [])


Connected-component : (c : A) → Type (level-of-type A)
Connected-component {A} c = Σ[ a ꞉ A ] ∥ c ＝ a ∥₁
