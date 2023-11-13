{-# OPTIONS --safe #-}
module Meta.Search.Decidable where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Reflection
open import Meta.Search.Base public

open import Correspondences.Decidable
open Correspondences.Decidable public
  using ( decide ; ×-decision ; fun-decision )

open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Fin.Instances.FromNat
open import Data.List.Base
open import Data.List.Instances.FromProduct

private variable
  ℓ ℓ′ ℓa ℓb ℓc ℓd : Level
  T : Type ℓ
  A : Type ℓa
  B : Type ℓb

instance
  Tactic-decide : Tactic-desc (quote Dec) none
  Tactic-decide .Tactic-desc.args-length = 2
  Tactic-decide .Tactic-desc.goal-selector = 1
  Tactic-decide .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-decide .Tactic-desc.instance-helper = quote decide
  Tactic-decide .Tactic-desc.instance-name = quote Dec

decide-tactic-worker = search-tactic-worker Tactic-decide
macro decide! = decide-tactic-worker

instance
  decomp-dec-× : goal-decomposition (quote Dec) (A × B)
  decomp-dec-× = decomp (quote ×-decision)
    [ `search (quote Dec) , `search (quote Dec) ]

  decomp-dec-neg : goal-decomposition (quote Dec) (¬ A)
  decomp-dec-neg = decomp (quote ¬-decision) [ `search (quote Dec) ]

  decomp-dec-fun : goal-decomposition (quote Dec) (A → B)
  decomp-dec-fun = decomp (quote fun-decision) [ `search (quote Dec) , `search (quote Dec) ]

  decomp-dec-lift : goal-decomposition (quote Dec) (Lift ℓ A)
  decomp-dec-lift = decomp (quote lift-decision) [ `search (quote Dec) ]

  decomp-dec-uni : goal-decomposition (quote Dec) (Type ℓ)
  decomp-dec-uni = decomp (quote universe-decision) []

-- Usage
private
  module _ ⦃ A? : Dec A ⦄ ⦃ B? : Dec B ⦄ where
    _ : Dec (¬ A → B × A)
    _ = decide!
