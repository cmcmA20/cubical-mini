{-# OPTIONS --safe #-}
module Meta.Search.Finite.Bishop where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Reflection
open import Meta.Search.Base public
open import Meta.Search.Discrete
open import Meta.Search.Exhaustible
open import Meta.Search.HLevel
open import Meta.Search.Omniscient
open import Meta.Variadic

open import Structures.FinSet
open Structures.FinSet public
  using (FinSet; fin-set)

open import Correspondences.Finite.Bishop
open Correspondences.Finite.Bishop public
  using ( is-bishop-finite
        ; fin₁ ; cardinality ; enumeration₁
        ; bishop-finite ; is-bishop-finite→omniscient₁ ; finite-pi-fin
        ; lift-is-bishop-finite ; ×-is-bishop-finite ; Π-is-bishop-finite
        ; fun-is-bishop-finite ; Σ-is-bishop-finite ; is-bishop-finite-≃ )
open import Correspondences.Omniscient

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Fin.Computational.Instances.FromNat

private variable
  ℓ ℓ′ ℓa ℓb ℓc ℓd : Level
  T : Type ℓ
  A : Type ℓa
  B : A → Type ℓb
  n : HLevel

instance
  Tactic-finite : Tactic-desc (quote is-bishop-finite) none
  Tactic-finite .Tactic-desc.args-length = 2
  Tactic-finite .Tactic-desc.goal-selector = 1
  Tactic-finite .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-finite .Tactic-desc.instance-helper = quote bishop-finite
  Tactic-finite .Tactic-desc.instance-name = quote is-bishop-finite

finite-tactic-worker = search-tactic-worker Tactic-finite
macro finite! = finite-tactic-worker

fin-set! : (A : Type ℓ) {@(tactic finite-tactic-worker) fi : is-bishop-finite A} → FinSet ℓ
fin-set! A {fi} = fin-set A fi

instance
  decomp-fin-lift : goal-decomposition (quote is-bishop-finite) (Lift ℓ′ A)
  decomp-fin-lift = decomp (quote lift-is-bishop-finite) [ `search (quote lift-is-bishop-finite) ]

  decomp-fin-fun : {B : Type ℓb} → goal-decomposition (quote is-bishop-finite) (A → B)
  decomp-fin-fun = decomp (quote fun-is-bishop-finite)
    [ `search (quote is-bishop-finite) , `search (quote is-bishop-finite) ]

  decomp-fin-Π : goal-decomposition (quote is-bishop-finite) (∀ a → B a)
  decomp-fin-Π = decomp (quote Π-is-bishop-finite)
    [ `search (quote is-bishop-finite) , `search-under 1 (quote is-bishop-finite) ]

  decomp-fin-× : {B : Type ℓb} → goal-decomposition (quote is-bishop-finite) (A × B)
  decomp-fin-× = decomp (quote ×-is-bishop-finite)
    [ `search (quote is-bishop-finite) , `search (quote is-bishop-finite) ]

  decomp-fin-Σ : goal-decomposition (quote is-bishop-finite) (Σ A B)
  decomp-fin-Σ = decomp (quote Σ-is-bishop-finite)
    [ `search (quote is-bishop-finite) , `search-under 1 (quote is-bishop-finite) ]

  decomp-fin→omn₁ : goal-decomposition (quote Omniscient₁) A
  decomp-fin→omn₁ = decomp (quote is-bishop-finite→omniscient₁) [ `search (quote is-bishop-finite) ]

  decomp-fin→dis : goal-decomposition (quote is-discrete) A
  decomp-fin→dis = decomp (quote is-bishop-finite→is-discrete) [ `search (quote is-bishop-finite) ]

  proj-fin-finset : Struct-proj-desc (quote is-bishop-finite) none (quote FinSet.carrier) true
  proj-fin-finset .Struct-proj-desc.struct-name = quote FinSet
  proj-fin-finset .Struct-proj-desc.struct-args-length = 1
  proj-fin-finset .Struct-proj-desc.goal-projection = quote FinSet.has-is-bishop-finite
  proj-fin-finset .Struct-proj-desc.projection-args-length = 2
  proj-fin-finset .Struct-proj-desc.carrier-selector = 1


-- Usage
private
  module _ {A : FinSet ℓa} {B : A →̇ FinSet ℓb} where
    _ : is-of-hlevel 3 (A →̇ A)
    _ = hlevel!

    _ : is-discrete (A ×̇ A)
    _ = discrete!

    _ : is-bishop-finite (A →̇ A →̇ A)
    _ = finite!

    _ : Omniscient₁ {ℓ} Π[ B ]
    _ = omni₁!

    _ : Exhaustible {ℓ} (A ×̇ A)
    _ = exhaust!
