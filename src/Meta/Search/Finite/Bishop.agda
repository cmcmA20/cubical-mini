{-# OPTIONS --safe #-}
module Meta.Search.Finite.Bishop where

open import Meta.Prelude

open import Meta.Reflection.Base
open import Meta.Search.Base public
open import Meta.Search.Discrete
open import Meta.Search.Exhaustible
open import Meta.Search.HLevel
open import Meta.Search.Omniscient

open import Structures.FinSet
open Structures.FinSet public
  using ( FinSet; fin-set ; Underlying-FinSet ; H-Level-FinSet )

open import Correspondences.Finite.Bishop
open Correspondences.Finite.Bishop public
  using ( is-bishop-finite ; fin₁ ; cardinality ; enumeration₁
        ; bishop-finite ; H-Level-is-bishop-finite
        ; is-bishop-finite→omniscient₁
        ; lift-is-bishop-finite ; ×-is-bishop-finite ; Π-is-bishop-finite
        ; fun-is-bishop-finite ; Σ-is-bishop-finite ; ≃→is-bishop-finite )
open import Correspondences.Finite.ManifestBishop
open import Correspondences.Omniscient

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Empty.Base as ⊥

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : A → Type ℓᵇ
  n : HLevel

instance
  Tactic-bishop-finite : Tactic-desc (quote is-bishop-finite) none
  Tactic-bishop-finite .Tactic-desc.args-length = 2
  Tactic-bishop-finite .Tactic-desc.goal-selector = 1
  Tactic-bishop-finite .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-bishop-finite .Tactic-desc.instance-helper = quote bishop-finite
  Tactic-bishop-finite .Tactic-desc.instance-name = quote is-bishop-finite

bishop-finite-tactic-worker = search-tactic-worker Tactic-bishop-finite
macro bishop-finite! = bishop-finite-tactic-worker

fin-set! : (A : Type ℓ) {@(tactic bishop-finite-tactic-worker) fi : is-bishop-finite A} → FinSet ℓ
fin-set! A {fi} = fin-set A fi

instance
  decomp-fin₁-lift : goal-decomposition (quote is-bishop-finite) (Lift ℓ A)
  decomp-fin₁-lift = decomp (quote lift-is-bishop-finite) [ `search (quote is-bishop-finite) ]

  decomp-fin₁-fun : {B : Type ℓᵇ} → goal-decomposition (quote is-bishop-finite) (A → B)
  decomp-fin₁-fun = decomp (quote fun-is-bishop-finite)
    [ `search (quote is-bishop-finite) , `search (quote is-bishop-finite) ]

  decomp-fin₁-Π : goal-decomposition (quote is-bishop-finite) (∀ a → B a)
  decomp-fin₁-Π = decomp (quote Π-is-bishop-finite)
    [ `search (quote is-bishop-finite) , `search-under 1 (quote is-bishop-finite) ]

  decomp-fin₁-× : {B : Type ℓᵇ} → goal-decomposition (quote is-bishop-finite) (A × B)
  decomp-fin₁-× = decomp (quote ×-is-bishop-finite)
    [ `search (quote is-bishop-finite) , `search (quote is-bishop-finite) ]

  decomp-fin₁-Σ : goal-decomposition (quote is-bishop-finite) Σ[ B ]
  decomp-fin₁-Σ = decomp (quote Σ-is-bishop-finite)
    [ `search (quote is-bishop-finite) , `search-under 1 (quote is-bishop-finite) ]

  -- decomp-dec-prop→fin₁ : goal-decomposition (quote is-bishop-finite) A
  -- decomp-dec-prop→fin₁ = decomp (quote decidable-prop→is-bishop-finite)
  --   [ `search (quote is-of-hlevel) , `search (quote Dec) ]

  decomp-fin₁→pathP : ∀ {A : I → Type ℓ} {x y} → goal-decomposition (quote is-bishop-finite) ＜ x ／ A ＼ y ＞
  decomp-fin₁→pathP = decomp (quote pathP-is-bishop-finite)
    [ `search (quote is-bishop-finite) , `meta , `meta ]

  decomp-fin₁→omn₁ : goal-decomposition (quote Omniscient₁) A
  decomp-fin₁→omn₁ = decomp (quote is-bishop-finite→omniscient₁) [ `search (quote is-bishop-finite) ]

  decomp-fin₁→dis : goal-decomposition (quote is-discrete) A
  decomp-fin₁→dis = decomp (quote is-bishop-finite→is-discrete) [ `search (quote is-bishop-finite) ]

  decomp-fin₁→fin : goal-decomposition (quote is-bishop-finite) A
  decomp-fin₁→fin = decomp (quote manifest-bishop-finite→is-bishop-finite) [ `search (quote Manifest-bishop-finite) ]

  proj-fin₁-finset : Struct-proj-desc (quote is-bishop-finite) none (quote FinSet.carrier) true
  proj-fin₁-finset .Struct-proj-desc.struct-name = quote FinSet
  proj-fin₁-finset .Struct-proj-desc.struct-args-length = 1
  proj-fin₁-finset .Struct-proj-desc.goal-projection = quote FinSet.has-bishop-finite
  proj-fin₁-finset .Struct-proj-desc.projection-args-length = 2
  proj-fin₁-finset .Struct-proj-desc.carrier-selector = 1


-- Usage
private
  module _ {A : FinSet ℓᵃ} {B : A →̇ FinSet ℓᵇ} where
    _ : is-groupoid (A →̇ A)
    _ = hlevel!

    _ : is-discrete (A ×̇ A)
    _ = discrete!

    _ : is-bishop-finite (A →̇ A →̇ A)
    _ = bishop-finite!

    _ : Omniscient₁ {ℓ} Π[ B ]
    _ = omni₁!

    _ : Exhaustible {ℓ} (A ×̇ A)
    _ = exhaust!

    _ : ∀{x y : ⌞ A ⌟} → is-bishop-finite (x ＝ y)
    _ = bishop-finite!
