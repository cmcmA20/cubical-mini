{-# OPTIONS --safe #-}
module Meta.Search.Finite.ManifestBishop where

open import Meta.Prelude

open import Meta.Reflection.Base
open import Meta.Search.Base public
open import Meta.Search.Discrete
open import Meta.Search.Exhaustible
open import Meta.Search.HLevel
open import Meta.Search.Omniscient

open import Structures.FinOrd public
  using ( FinOrd; fin-ord ; Underlying-FinOrd ; H-Level-FinOrd )

open import Correspondences.Finite.ManifestBishop public
  using ( Manifest-bishop-finite ; fin ; cardinality ; enumeration
        ; manifest-bishop-finite
        ; lift-manifest-bishop-finite ; ×-manifest-bishop-finite
        ; fun-manifest-bishop-finite ; Π-manifest-bishop-finite
        ; Σ-manifest-bishop-finite
        ; manifest-bishop-finite→omniscient₁ ; manifest-bishop-finite→is-discrete
        ; manifest-bishop-finite-≃ )
open import Correspondences.Omniscient

open import Data.Bool.Base
open import Data.Empty.Base as ⊥

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : A → Type ℓᵇ
  n : HLevel

instance
  Tactic-manifest-bishop-finite : Tactic-desc (quote Manifest-bishop-finite) none
  Tactic-manifest-bishop-finite .Tactic-desc.args-length = 2
  Tactic-manifest-bishop-finite .Tactic-desc.goal-selector = 1
  Tactic-manifest-bishop-finite .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-manifest-bishop-finite .Tactic-desc.instance-helper = quote manifest-bishop-finite
  Tactic-manifest-bishop-finite .Tactic-desc.instance-name = quote Manifest-bishop-finite

manifest-bishop-finite-tactic-worker = search-tactic-worker Tactic-manifest-bishop-finite
macro manifest-bishop-finite! = manifest-bishop-finite-tactic-worker

fin-ord! : (A : Type ℓ) {@(tactic manifest-bishop-finite-tactic-worker) fi : Manifest-bishop-finite A} → FinOrd ℓ
fin-ord! A {fi} = fin-ord A fi

instance
  decomp-fin-lift : goal-decomposition (quote Manifest-bishop-finite) (Lift ℓ A)
  decomp-fin-lift = decomp (quote lift-manifest-bishop-finite) [ `search (quote Manifest-bishop-finite) ]

  decomp-fin-× : {B : Type ℓᵇ} → goal-decomposition (quote Manifest-bishop-finite) (A × B)
  decomp-fin-× = decomp (quote ×-manifest-bishop-finite)
    [ `search (quote Manifest-bishop-finite) , `search (quote Manifest-bishop-finite) ]

  decomp-fin→omn₁ : goal-decomposition (quote Omniscient₁) A
  decomp-fin→omn₁ = decomp (quote manifest-bishop-finite→omniscient₁) [ `search (quote Manifest-bishop-finite) ]

  decomp-fin→dis : goal-decomposition (quote is-discrete) A
  decomp-fin→dis = decomp (quote manifest-bishop-finite→is-discrete) [ `search (quote Manifest-bishop-finite) ]

  decomp-fin-fun : {B : Type ℓᵇ} → goal-decomposition (quote Manifest-bishop-finite) (A → B)
  decomp-fin-fun = decomp (quote fun-manifest-bishop-finite)
    [ `search (quote Manifest-bishop-finite) , `search (quote Manifest-bishop-finite) ]

  decomp-fin-Π : goal-decomposition (quote Manifest-bishop-finite) (∀ a → B a)
  decomp-fin-Π = decomp (quote Π-manifest-bishop-finite)
    [ `search (quote Manifest-bishop-finite) , `search-under 1 (quote Manifest-bishop-finite) ]

  decomp-fin-Σ : goal-decomposition (quote Manifest-bishop-finite) (Σ A B)
  decomp-fin-Σ = decomp (quote Σ-manifest-bishop-finite)
    [ `search (quote Manifest-bishop-finite) , `search-under 1 (quote Manifest-bishop-finite) ]

  proj-fin-finset : Struct-proj-desc (quote Manifest-bishop-finite) none (quote FinOrd.carrier) true
  proj-fin-finset .Struct-proj-desc.struct-name = quote FinOrd
  proj-fin-finset .Struct-proj-desc.struct-args-length = 1
  proj-fin-finset .Struct-proj-desc.goal-projection = quote FinOrd.has-manifest-bishop-finite
  proj-fin-finset .Struct-proj-desc.projection-args-length = 2
  proj-fin-finset .Struct-proj-desc.carrier-selector = 1


-- Usage
private
  module _ {A : FinOrd ℓᵃ} {B : A →̇ FinOrd ℓᵇ} where
    _ : is-groupoid (A →̇ A)
    _ = hlevel!

    _ : is-discrete (A ×̇ A)
    _ = discrete!

    _ : Manifest-bishop-finite (A →̇ A →̇ A)
    _ = manifest-bishop-finite!

    _ : Omniscient₁ {ℓ} Π[ B ]
    _ = omni₁!

    _ : Exhaustible {ℓ} (A ×̇ A)
    _ = exhaust!
