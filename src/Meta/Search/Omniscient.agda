{-# OPTIONS --safe #-}
module Meta.Search.Omniscient where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Reflection
open import Meta.Search.Base public
open import Meta.Search.Decidable
open import Meta.Search.Exhaustible
open import Meta.Search.HLevel

open import Correspondences.Omniscient
open Correspondences.Omniscient public
  using ( Omniscient₁ ; omniscient₁-β ; omniscient₁-η
        ; omni₁
        ; ∃-decision ; omniscient₁→exhaustible )

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.FinSub.Instances.FromNat
open import Data.List.Instances.FromProduct

open import Truncation.Propositional.Base

private variable
  ℓ ℓ′ ℓa ℓb ℓc ℓd : Level
  T : Type ℓ
  A : Type ℓa
  B : A → Type ℓb
  C : (a : A) (b : B a) → Type ℓc
  D : (a : A) (b : B a) (c : C a b) → Type ℓd
  n : HLevel

instance
  Tactic-omni₁ : Tactic-desc (quote Omniscient₁) none
  Tactic-omni₁ .Tactic-desc.args-length = 3
  Tactic-omni₁ .Tactic-desc.goal-selector = 2
  Tactic-omni₁ .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-omni₁ .Tactic-desc.instance-helper = quote omni₁
  Tactic-omni₁ .Tactic-desc.instance-name = quote Omniscient₁

omni₁-tactic-worker = search-tactic-worker Tactic-omni₁
macro omni₁! = omni₁-tactic-worker

instance
  decomp-omn₁→exh : goal-decomposition (quote Exhaustible) A
  decomp-omn₁→exh = decomp (quote omniscient₁→exhaustible)
    [ `search (quote Omniscient₁) ]

  decomp-dec-∃ : goal-decomposition (quote Dec) (∃[ a ꞉ A ] B a )
  decomp-dec-∃ = decomp (quote ∃-decision) [ `search-under 1 (quote Dec) , `search (quote Omniscient₁) ]

-- TODO more decompositions

-- Usage
private
  module _ ⦃ A-omn : Omniscient₁ {ℓ = ℓ} A ⦄ where
    _ : Omniscient₁ A
    _ = omni₁!

    _ : Exhaustible A
    _ = exhaust!
