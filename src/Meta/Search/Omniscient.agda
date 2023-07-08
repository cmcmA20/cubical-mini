{-# OPTIONS --safe #-}
module Meta.Search.Omniscient where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Reflection
open import Meta.Search.Base public
open import Meta.Search.Exhaustible
open import Meta.Search.HLevel

open import Correspondences.Omniscient
open Correspondences.Omniscient public
  using ( is-omniscient
        ; is-omniscient-β ; is-omniscient-η
        ; omni )

open import Data.Empty.Base as ⊥
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
  Tactic-omni : Tactic-desc (quote is-omniscient) none
  Tactic-omni .Tactic-desc.args-length = 3
  Tactic-omni .Tactic-desc.goal-selector = 2
  Tactic-omni .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-omni .Tactic-desc.instance-helper = quote omni

omni-tactic-worker = search-tactic-worker Tactic-omni
macro omni! = omni-tactic-worker

instance
  decomp-omn→exh : goal-decomposition (quote is-exhaustible) A
  decomp-omn→exh = decomp (quote is-omniscient→is-exhaustible) [ `search (quote is-omniscient) ]

-- is-fin-set→is-omniscient

-- TODO more decompositions

-- Usage
private
  module _ ⦃ A-omn : is-omniscient {ℓ′ = ℓ′} A ⦄ where
    _ : is-omniscient {ℓ′ = ℓ′} A
    _ = omni!

    _ : is-exhaustible {ℓ′ = ℓ′} A
    _ = exhaust!
