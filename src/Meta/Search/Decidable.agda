{-# OPTIONS --safe #-}
module Meta.Search.Decidable where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel
open import Foundations.Sigma

open import Meta.Literals.FromProduct
open import Meta.Reflection
open import Meta.Search.Base public
open import Meta.Search.HLevel

open import Correspondences.Nullary.Decidable
open Correspondences.Nullary.Decidable public
  using ( is-decidable-at-hlevel ; Decision ; is-discrete
        ; decision-β ; decision-η ; is-discrete-β ; is-discrete-η
        ; decide ; ×-decision ; →-decision
        ; is-discrete-injection ; is-discrete-embedding )

open import Data.Dec.Base
open import Data.Empty.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Maybe.Base

private variable
  ℓ ℓ′ ℓa ℓb ℓc ℓd : Level
  T : Type ℓ
  A : Type ℓa
  B : A → Type ℓb
  C : (a : A) (b : B a) → Type ℓc
  D : (a : A) (b : B a) (c : C a b) → Type ℓd
  n : HLevel

instance
  Tactic-dec : Tactic-desc (quote is-decidable-at-hlevel)
  Tactic-dec .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-dec .Tactic-desc.instance-fallback-helper = quote decide
  Tactic-dec .Tactic-desc.upwards-closure = nothing

dec-tactic-worker = search-tactic-worker Tactic-dec
macro dec! = dec-tactic-worker

_≟_ : { @(tactic dec-tactic-worker) di : is-discrete A } → (x y : A) → Dec (x ＝ y)
_≟_ {di} = is-discrete-β di

hedberg-helper : (n : HLevel) → is-discrete A → is-of-hlevel (2 + n) A
hedberg-helper n A-d = is-of-hlevel-+-left 2 n (is-discrete→is-set A-d)

instance
  decomp-dec₁-lift : goal-decomposition (quote is-decidable-at-hlevel) (Lift ℓ′ A)
  decomp-dec₁-lift = decomp (quote lift-is-discrete)
    [ `search (quote is-decidable-at-hlevel) ]

  decomp-dec₁-× : {B : Type ℓb} → goal-decomposition (quote is-decidable-at-hlevel) (A × B)
  decomp-dec₁-× = decomp (quote ×-is-discrete)
    [ `search (quote is-decidable-at-hlevel) , `search (quote is-decidable-at-hlevel) ]

  decomp-dec₁-Σ : goal-decomposition (quote is-decidable-at-hlevel) (Σ A B)
  decomp-dec₁-Σ = decomp (quote Σ-is-discrete)
    [ `search (quote is-decidable-at-hlevel) , `search-under 1 (quote is-decidable-at-hlevel) ]

  decomp-dec₁-suc : goal-decomposition (quote is-decidable-at-hlevel) A
  decomp-dec₁-suc = decomp (quote is-decidable-at-hlevel-suc)
    [ `level-minus 2 , `search (quote is-decidable-at-hlevel) ]

  decomp-dec₀-× : {B : Type ℓb} → goal-decomposition (quote is-decidable-at-hlevel) (A × B)
  decomp-dec₀-× = decomp (quote ×-decision)
    [ `search (quote is-decidable-at-hlevel) , `search (quote is-decidable-at-hlevel) ]

  decomp-dec₀-fun : {B : Type ℓb} → goal-decomposition (quote is-decidable-at-hlevel) (A → B)
  decomp-dec₀-fun = decomp (quote →-decision)
    [ `search (quote is-decidable-at-hlevel) , `search (quote is-decidable-at-hlevel) ]

  decomp-hlevel-dec : goal-decomposition (quote is-of-hlevel) A
  decomp-hlevel-dec = decomp (quote hedberg-helper)
    [ `level-minus 2 , `search (quote is-decidable-at-hlevel) ]

-- Usage
private
  module _ ⦃ A-dis : is-discrete A ⦄ {B : Type ℓb} ⦃ B-dis : is-discrete B ⦄
           {C : Type ℓc} ⦃ C-d : Decision C ⦄ where
    _ : is-of-hlevel 2 (A → A → A)
    _ = hlevel!

    _ : is-of-hlevel 4 (A × A)
    _ = hlevel!

    _ : is-of-hlevel 2 (Lift ℓb A ≃ Lift ℓa B)
    _ = hlevel!

    _ : is-discrete (A × A × A × A)
    _ = dec!

    _ : is-decidable-at-hlevel 4 A
    _ = dec!
