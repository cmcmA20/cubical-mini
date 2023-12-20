{-# OPTIONS --safe #-}
module Meta.Search.Decidable where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Reflection.Base
open import Meta.Search.Base public

open import Correspondences.Decidable
open Correspondences.Decidable public
  using ( Decidableⁿ; Decidable ; Reflectsⁿ ; Reflects
        ; decide ; ×-decision ; fun-decision )

open import Data.Dec.Base
open import Data.Empty.Base

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

instance
  Tactic-decide : Tactic-desc (quote Dec) none
  Tactic-decide .Tactic-desc.args-length = 2
  Tactic-decide .Tactic-desc.goal-selector = 1
  Tactic-decide .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-decide .Tactic-desc.instance-helper = quote decide
  Tactic-decide .Tactic-desc.instance-name = quote Dec

decide-tactic-worker = search-tactic-worker Tactic-decide
macro decide! = decide-tactic-worker

caseᵈ_of_ : (A : Type ℓᵃ) { @(tactic decide-tactic-worker) d : Dec A }
          → (Dec A → B) → B
caseᵈ_of_ A {d} f = f d
{-# INLINE caseᵈ_of_ #-}

caseᵈ_return_of_ : (A : Type ℓ) { @(tactic decide-tactic-worker) d : Dec A }
                   (B : Dec A → Type ℓ) → (∀ x → B x) → B d
caseᵈ_return_of_ A {d} B f = f d
{-# INLINE caseᵈ_return_of_ #-}

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


-- Usage
private
  module _ ⦃ A? : Dec A ⦄ ⦃ B? : Dec B ⦄ where
    _ : Dec (¬ A → B × A)
    _ = decide!
