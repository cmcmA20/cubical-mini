{-# OPTIONS --safe #-}
module Meta.Search.Finite.Bishop where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel
open import Foundations.Sigma

open import Meta.Literals.FromProduct
open import Meta.Reflection
open import Meta.Search.Base public
open import Meta.Search.Decidable
open import Meta.Search.HLevel

open import Structures.FinSet
open import Structures.FinSet public
  using (FinSet; fin-set)

open import Correspondences.Nullary.Finite.Bishop
open Correspondences.Nullary.Finite.Bishop public
  using ( is-fin-set-at-hlevel ; is-fin-set
        ; is-fin-set-β ; is-fin-set-η
        ; fin ; cardinality ; enumeration
        ; finite )

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
  n : HLevel

instance
  Tactic-finite : Tactic-desc (quote is-fin-set-at-hlevel)
  Tactic-finite .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-finite .Tactic-desc.instance-fallback-helper = quote finite
  Tactic-finite .Tactic-desc.upwards-closure = nothing

finite-tactic-worker = search-tactic-worker Tactic-finite
macro finite! = finite-tactic-worker

fin-set! : (A : Type ℓ) {@(tactic finite-tactic-worker) fi : is-fin-set-at-hlevel 0 A} → FinSet ℓ
fin-set! A {fi} = fin-set A fi

instance
  decomp-hlevel-is-fin-set : goal-decomposition (quote is-of-hlevel) (is-fin-set A)
  decomp-hlevel-is-fin-set = decomp (quote is-fin-set-is-of-hlevel) [ `level-minus 1 ]

  decomp-fin-lift : goal-decomposition (quote is-fin-set-at-hlevel) (Lift ℓ′ A)
  decomp-fin-lift = decomp (quote lift-is-fin-set) [ `search (quote lift-is-fin-set) ]

  decomp-fin-Π : goal-decomposition (quote is-fin-set-at-hlevel) (∀ a → B a)
  decomp-fin-Π = decomp (quote Π-is-fin-set)
    [ `search (quote is-fin-set-at-hlevel) , `search-under 1 (quote is-fin-set-at-hlevel) ]

  decomp-fin-× : {B : Type ℓb} → goal-decomposition (quote is-fin-set-at-hlevel) (A × B)
  decomp-fin-× = decomp (quote ×-is-fin-set)
    [ `search (quote is-fin-set-at-hlevel) , `search (quote is-fin-set-at-hlevel) ]

  decomp-fin-Σ : goal-decomposition (quote is-fin-set-at-hlevel) (Σ A B)
  decomp-fin-Σ = decomp (quote Σ-is-fin-set)
    [ `search (quote is-fin-set-at-hlevel) , `search-under 1 (quote is-fin-set-at-hlevel) ]

  decomp-hlevel-fin : goal-decomposition (quote is-of-hlevel) A
  decomp-hlevel-fin = decomp (quote is-fin-set→is-of-hlevel )
    [ `level-minus 2 , `search (quote is-fin-set-at-hlevel) ]

  proj-fin-finset : Struct-proj-desc (quote is-fin-set-at-hlevel) (quote FinSet-carrier)
  proj-fin-finset .Struct-proj-desc.struct-name = quote FinSet
  proj-fin-finset .Struct-proj-desc.project-goal = quote FinSet-carrier-is-fin-set
  proj-fin-finset .Struct-proj-desc.get-level ty = do
    def (quote FinSet) (ell v∷ []) ← reduce ty
      where _ → backtrack [ "Type of thing isn't FinSet, it is " , termErr ty ]
    normalise (lit (nat 0))
  proj-fin-finset .Struct-proj-desc.get-argument (_ ∷ it v∷ []) = pure it
  proj-fin-finset .Struct-proj-desc.get-argument _ = typeError []

  -- FIXME so much duplication
  proj-dec₁-finset : Struct-proj-desc (quote is-decidable-at-hlevel) (quote FinSet-carrier)
  proj-dec₁-finset .Struct-proj-desc.struct-name = quote FinSet
  proj-dec₁-finset .Struct-proj-desc.project-goal = quote FinSet-carrier-is-discrete
  proj-dec₁-finset .Struct-proj-desc.get-level ty = do
    def (quote FinSet) (ell v∷ []) ← reduce ty
      where _ → backtrack [ "Type of thing isn't FinSet, it is " , termErr ty ]
    normalise (lit (nat 0))
  proj-dec₁-finset .Struct-proj-desc.get-argument (_ ∷ it v∷ []) = pure it
  proj-dec₁-finset .Struct-proj-desc.get-argument _ = typeError []

-- Usage
private
  module _ {A : FinSet ℓ} {B : ⌞ A ⌟ → FinSet ℓ′} where
    _ : is-of-hlevel 3 (⌞ A ⌟ → ⌞ A ⌟)
    _ = hlevel!

    _ : is-discrete (⌞ A ⌟ × ⌞ A ⌟)
    _ = decide!

    _ : is-fin-set ⌞ A ⌟
    _ = finite!

    _ : is-fin-set (⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟)
    _ = finite!
