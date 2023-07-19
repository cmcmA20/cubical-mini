{-# OPTIONS --safe #-}
module Meta.Search.Finite.Bishop where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Literals.FromProduct
open import Meta.Reflection
open import Meta.Search.Base public
open import Meta.Search.Discrete
open import Meta.Search.Exhaustible
open import Meta.Search.HLevel
open import Meta.Search.Omniscient

open import Structures.FinSet
open Structures.FinSet public
  using (FinSet; fin-set)

open import Correspondences.Finite.Bishop
open Correspondences.Finite.Bishop public
  using ( is-fin-set ; is-fin-set-β ; is-fin-set-η
        ; fin ; cardinality ; enumeration
        ; finite ; is-fin-set→omniscient₁ ; finite-pi-fin )
open import Correspondences.Omniscient

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Fin.Instances.FromNat
open import Data.List.Instances.FromProduct

private variable
  ℓ ℓ′ ℓa ℓb ℓc ℓd : Level
  T : Type ℓ
  A : Type ℓa
  B : A → Type ℓb
  n : HLevel

instance
  Tactic-finite : Tactic-desc (quote is-fin-set) none
  Tactic-finite .Tactic-desc.args-length = 2
  Tactic-finite .Tactic-desc.goal-selector = 1
  Tactic-finite .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-finite .Tactic-desc.instance-helper = quote finite

finite-tactic-worker = search-tactic-worker Tactic-finite
macro finite! = finite-tactic-worker

fin-set! : (A : Type ℓ) {@(tactic finite-tactic-worker) fi : is-fin-set A} → FinSet ℓ
fin-set! A {fi} = fin-set A fi

instance
  decomp-hlevel-is-fin-set : goal-decomposition (quote is-of-hlevel) (is-fin-set A)
  decomp-hlevel-is-fin-set = decomp (quote is-fin-set-is-of-hlevel) [ `level-minus 1 ]

  decomp-fin-lift : goal-decomposition (quote is-fin-set) (Lift ℓ′ A)
  decomp-fin-lift = decomp (quote lift-is-fin-set) [ `search (quote lift-is-fin-set) ]

  decomp-fin-fun : {B : Type ℓb} → goal-decomposition (quote is-fin-set) (A → B)
  decomp-fin-fun = decomp (quote fun-is-fin-set)
    [ `search (quote is-fin-set) , `search (quote is-fin-set) ]

  decomp-fin-Π : goal-decomposition (quote is-fin-set) (∀ a → B a)
  decomp-fin-Π = decomp (quote Π-is-fin-set)
    [ `search (quote is-fin-set) , `search-under 1 (quote is-fin-set) ]

  decomp-fin-× : {B : Type ℓb} → goal-decomposition (quote is-fin-set) (A × B)
  decomp-fin-× = decomp (quote ×-is-fin-set)
    [ `search (quote is-fin-set) , `search (quote is-fin-set) ]

  decomp-fin-Σ : goal-decomposition (quote is-fin-set) (Σ A B)
  decomp-fin-Σ = decomp (quote Σ-is-fin-set)
    [ `search (quote is-fin-set) , `search-under 1 (quote is-fin-set) ]

  decomp-fin→omn₁ : goal-decomposition (quote Omniscient₁) A
  decomp-fin→omn₁ = decomp (quote is-fin-set→omniscient₁) [ `search (quote is-fin-set) ]

  decomp-fin→dis : goal-decomposition (quote is-discrete) A
  decomp-fin→dis = decomp (quote is-fin-set→is-discrete) [ `search (quote is-fin-set) ]

  proj-fin-finset : Struct-proj-desc (quote is-fin-set) none (quote FinSet.carrier) true
  proj-fin-finset .Struct-proj-desc.struct-name = quote FinSet
  proj-fin-finset .Struct-proj-desc.struct-args-length = 1
  proj-fin-finset .Struct-proj-desc.goal-projection = quote FinSet.carrier-is-fin-set
  proj-fin-finset .Struct-proj-desc.projection-args-length = 2
  proj-fin-finset .Struct-proj-desc.carrier-selector = 1


-- Usage
private
  module _ {A : FinSet ℓ} {B : ⌞ A ⌟ → FinSet ℓ′} where
    _ : is-of-hlevel 3 (⌞ A ⌟ → ⌞ A ⌟)
    _ = hlevel!

    _ : is-discrete (⌞ A ⌟ × ⌞ A ⌟)
    _ = discrete!

    _ : is-fin-set (⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟)
    _ = finite!

    _ : Omniscient₁ {ℓ′ = ℓ′} (Π[ a ꞉ ⌞ A ⌟ ] ⌞ B a ⌟)
    _ = omni₁!

    _ : Exhaustible {ℓ′ = ℓ′} (⌞ A ⌟ × ⌞ A ⌟)
    _ = exhaust!
