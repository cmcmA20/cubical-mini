{-# OPTIONS --safe #-}
module Data.Sum.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind
open import Meta.Search.Finite.Bishop
open import Meta.Search.Finite.ManifestBishop

open import Data.Fin.Computational.Closure
open import Data.Sum.Properties

open import Truncation.Propositional.Instances.Bind

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

⊎-manifest-bishop-finite : Manifest-bishop-finite A → Manifest-bishop-finite B → Manifest-bishop-finite (A ⊎ B)
⊎-manifest-bishop-finite afi bfi = fin $ ⊎-ap (enumeration afi) (enumeration bfi) ∙ₑ fin-coproduct

⊎-is-bishop-finite : is-bishop-finite A → is-bishop-finite B → is-bishop-finite (A ⊎ B)
⊎-is-bishop-finite afi bfi = fin₁ do
  aeq ← enumeration₁ afi
  beq ← enumeration₁ bfi
  pure $ ⊎-ap aeq beq ∙ₑ fin-coproduct

instance
  decomp-fin-⊎ : goal-decomposition (quote Manifest-bishop-finite) (A ⊎ B)
  decomp-fin-⊎ = decomp (quote ⊎-manifest-bishop-finite)
    [ `search (quote Manifest-bishop-finite) , `search (quote Manifest-bishop-finite) ]

  decomp-fin₁-⊎ : goal-decomposition (quote is-bishop-finite) (A ⊎ B)
  decomp-fin₁-⊎ = decomp (quote ⊎-is-bishop-finite)
    [ `search (quote is-bishop-finite) , `search (quote is-bishop-finite) ]
