{-# OPTIONS --safe #-}
module Data.Quotient.Set.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.HLevel
open import Meta.Underlying

open import Correspondences.Discrete

open import Data.Empty.Base
open import Data.Dec.Base as Dec
open import Data.Dec.Instances.HLevel
open import Data.List.Base

open import Data.Quotient.Set.Properties

private variable
  ℓ ℓᵃ : Level
  A : Type ℓᵃ
  R : Rel 2 ℓ A

/₂-is-discrete
  : (Rc : is-congruence R)
  → (∀ x y → Dec ⌞ R x y ⌟)
  → is-discrete (A / ⌞ R ⌟ₙ)
/₂-is-discrete {R} congr d = is-discrete-η $ elim₂-prop! λ x y →
  Dec.map (glue/ _ _) (λ f p → absurd (f ((effective {R = R} congr) .fst p))) (d x y)

-- FIXME nonmonotonic reasoning in decomps again
open import Meta.Search.Discrete
instance
  decomp-dis-list : goal-decomposition (quote is-discrete) (A / ⌞ R ⌟ₙ)
  decomp-dis-list = decomp (quote /₂-is-discrete) (`meta ∷ `search-under 2 (quote Dec) ∷ [])
