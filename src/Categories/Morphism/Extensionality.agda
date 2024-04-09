{-# OPTIONS --safe #-}
open import Categories.Base

module Categories.Morphism.Extensionality {o ℓ} {C : Precategory o ℓ} where

open import Foundations.Prelude
  hiding (_≅_)
open import Meta.Extensionality

open import Structures.n-Type

open import Categories.Morphism C

instance
  Extensional-≅
    : ∀ {ℓr} {a b}
    → ⦃ sa : Extensional (Hom a b) ℓr ⦄
    → Extensional (a ≅ b) ℓr
  Extensional-≅ ⦃ sa ⦄ .Pathᵉ a b = Pathᵉ sa (a .to) (b .to)
  Extensional-≅ ⦃ sa ⦄ .reflᵉ im = reflᵉ sa (im .to)
  Extensional-≅ ⦃ sa ⦄ .idsᵉ = set-identity-system
    (λ _ _ → Pathᵉ-is-of-hlevel 1 sa hlevel!)
    (λ p → ≅-path (sa .idsᵉ .to-path p))
