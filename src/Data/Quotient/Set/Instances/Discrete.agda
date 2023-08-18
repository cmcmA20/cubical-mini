{-# OPTIONS --safe #-}
module Data.Quotient.Set.Instances.Discrete where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel
open import Meta.Underlying

open import Correspondences.Discrete

open import Data.Empty.Base
open import Data.Dec.Base as Dec
open import Data.Dec.Instances.HLevel

open import Data.Quotient.Set.Properties

private variable
  ℓ ℓᵃ : Level
  A : Type ℓᵃ
  R : Corr 2 ℓ A

/₂-is-discrete
  : (R-c : is-congruence R)
  → (∀ x y → Dec (R x y))
  → is-discrete (A / R)
/₂-is-discrete R-c d = is-discrete-η $ elim₂-prop! λ x y →
  Dec.map (glue/ _ _) (λ f p → absurd (f $ (effective R-c ₑ⁻¹) .fst p)) $ d x y

-- TOOD honestly looks like a bad idea, it's impossible to reconstruct congruence proof
-- without further automation
-- open import Meta.Search.Discrete
-- instance
--   decomp-dis-list : goal-decomposition (quote is-discrete) (A / R)
--   decomp-dis-list = decomp (quote /₂-is-discrete) (`meta ∷ `search-under 2 (quote Dec) ∷ [])
