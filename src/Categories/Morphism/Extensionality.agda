{-# OPTIONS --safe #-}
open import Categories.Base

module Categories.Morphism.Extensionality {o ℓ} {C : Precategory o ℓ} where

open import Meta.Extensionality
open import Meta.Search.HLevel

open import Categories.Morphism C

Extensional-≅
  : ∀ {ℓr} {a b}
  → ⦃ sa : Extensional (Hom a b) ℓr ⦄
  → Extensional (a ≅ b) ℓr
Extensional-≅ ⦃ sa ⦄ .Pathᵉ a b = Pathᵉ sa (a .to) (b .to)
Extensional-≅ ⦃ sa ⦄ .reflᵉ im = reflᵉ sa (im .to)
Extensional-≅ ⦃ sa ⦄ .idsᵉ = set-identity-system
  (λ _ _ → Pathᵉ-is-of-hlevel 1 sa hlevel!)
  (λ p → ≅-path (sa .idsᵉ .to-path p))

instance
  extensionality-≅ : ∀ {a b} → Extensionality (a ≅ b)
  extensionality-≅ = record { lemma = quote Extensional-≅ }
