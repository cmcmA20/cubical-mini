{-# OPTIONS --safe #-}
module Data.Quotient.Set.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Data.Quotient.Set.Base

instance opaque
  H-Level-/₂
    : ∀{ℓᵃ ℓ}{A : Type ℓᵃ} {R : A → A → 𝒰 ℓ}
    → ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n (A / R)
  H-Level-/₂ ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 squash/
  {-# OVERLAPS H-Level-/₂ #-}

instance
  Extensional-/₂-map
    : ∀ {ℓ ℓ′ ℓ″ ℓr} {A : Type ℓ} {R : A → A → Type ℓ′} {B : Type ℓ″}
      ⦃ sf : Extensional (A → B) ℓr ⦄ ⦃ B-set : H-Level 2 B ⦄
    → Extensional (A / R → B) ℓr
  Extensional-/₂-map ⦃ sf ⦄ .Pathᵉ f g = sf .Pathᵉ (f ∘ ⦋_⦌) (g ∘ ⦋_⦌)
  Extensional-/₂-map ⦃ sf ⦄ .reflᵉ f = sf .reflᵉ (f ∘ ⦋_⦌)
  Extensional-/₂-map ⦃ sf ⦄ .idsᵉ .to-path h = fun-ext $ elim! (sf .idsᵉ .to-path h $ₚ_)
  Extensional-/₂-map ⦃ sf ⦄ .idsᵉ .to-path-over p =
    is-prop→pathᴾ (λ i → Pathᵉ-is-of-hlevel 1 sf (hlevel 2)) _ p
