{-# OPTIONS --safe #-}
module Meta.Search.Discrete where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Literals.FromProduct
open import Meta.Reflection
open import Meta.Search.Base public
open import Meta.Search.Decidable
open import Meta.Search.HLevel

open import Correspondences.Discrete
open Correspondences.Discrete public
  using ( is-discrete ; is-discrete-β ; is-discrete-η
        ; is-discrete-injection ; is-discrete-embedding )

open import Data.Dec.Base
open import Data.Fin.Instances.FromNat
open import Data.List.Instances.FromProduct

private variable
  ℓ ℓ′ ℓa ℓb ℓc ℓd : Level
  T : Type ℓ
  A : Type ℓa
  B : A → Type ℓb
  C : (a : A) (b : B a) → Type ℓc
  D : (a : A) (b : B a) (c : C a b) → Type ℓd
  n : HLevel

instance
  Tactic-discrete : Tactic-desc (quote is-discrete) none
  Tactic-discrete .Tactic-desc.args-length = 2
  Tactic-discrete .Tactic-desc.goal-selector = 1
  Tactic-discrete .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-discrete .Tactic-desc.instance-helper = quote discrete

discrete-tactic-worker = search-tactic-worker Tactic-discrete
macro discrete! = discrete-tactic-worker

_≟_ : { @(tactic discrete-tactic-worker) di : is-discrete A } → (x y : A) → Dec (x ＝ y)
_≟_ {di} = is-discrete-β di

dec-helper : is-discrete A → (x y : A) → Dec (x ＝ y)
dec-helper = is-discrete-β

hedberg-helper : (n : HLevel) → is-discrete A → is-of-hlevel (2 + n) A
hedberg-helper n di = is-of-hlevel-+-left 2 n (is-discrete→is-set di)

instance
  decomp-dis-lift : goal-decomposition (quote is-discrete) (Lift ℓ′ A)
  decomp-dis-lift = decomp (quote lift-is-discrete) [ `search (quote is-discrete) ]

  decomp-dis-× : {B : Type ℓb} → goal-decomposition (quote is-discrete) (A × B)
  decomp-dis-× = decomp (quote ×-is-discrete)
    [ `search (quote is-discrete) , `search (quote is-discrete) ]

  decomp-dis-Σ : goal-decomposition (quote is-discrete) (Σ A B)
  decomp-dis-Σ = decomp (quote Σ-is-discrete)
    [ `search (quote is-discrete) , `search-under 1 (quote is-discrete) ]

  decomp-hlevel-hedberg : goal-decomposition (quote is-of-hlevel) A
  decomp-hlevel-hedberg = decomp (quote hedberg-helper)
    [ `level-minus 2 , `search (quote is-discrete) ]

  decomp-hlevel-dis : goal-decomposition (quote is-of-hlevel) (is-discrete A)
  decomp-hlevel-dis = decomp (quote is-discrete-is-of-hlevel) [ `level-minus 1 ]

  decomp-dec-eq : {x y : A} → goal-decomposition (quote Dec) (x ＝ y)
  decomp-dec-eq = decomp (quote dec-helper) [ `search (quote is-discrete) , `meta , `meta ]

-- Usage
private
  module _ ⦃ A-dis : is-discrete A ⦄ {B : A → Type ℓb} ⦃ B-dis : ∀{a} → is-discrete (B a) ⦄ where
    _ : is-discrete (A × A × A × A)
    _ = discrete!

    _ : is-discrete (Σ[ a ꞉ A ] B a × Lift ℓb A)
    _ = discrete!

    _ : is-set (Σ[ a ꞉ A ] B a ≃ Lift ℓb A)
    _ = hlevel!
