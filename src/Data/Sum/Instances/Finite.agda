{-# OPTIONS --safe #-}
module Data.Sum.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind
open import Meta.Search.Finite.Bishop

open import Data.Fin.Closure
open import Data.List.Base
open import Data.Sum.Properties

open import Truncation.Propositional

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

⊎-is-fin-set : is-fin-set A → is-fin-set B → is-fin-set (A ⊎ B)
⊎-is-fin-set afi bfi = fin do
  aeq ← enumeration afi
  beq ← enumeration bfi
  pure $ ⊎-ap aeq beq ∙ₑ fin-coproduct

instance
  decomp-fin-⊎ : goal-decomposition (quote is-fin-set) (A ⊎ B)
  decomp-fin-⊎ = decomp (quote ⊎-is-fin-set)
    (`search (quote is-fin-set) ∷ `search (quote is-fin-set) ∷ [])
