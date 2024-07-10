{-# OPTIONS --safe #-}
module Data.Container.Morphism where

open import Foundations.Prelude

open import Meta.Notation.Brackets

open import Data.Container.Base
open import Data.Container.Instances.Brackets

private variable
  ℓ ℓ′ s s′ p p′ : Level
  X  : Type ℓ

open Container

-- container morphism
record _⇒_ (C : Container s p) (C′ : Container s′ p′)
           : Type (s ⊔ p ⊔ s′ ⊔ p′) where
  constructor _▶_
  field
    shape    : Shape C → Shape C′
    position : ∀ {sh} → Position C′ (shape sh) → Position C sh

  ⟪_⟫→ : ⟦ C ⟧ X → ⟦ C′ ⟧ X
  ⟪ x , g ⟫→ = shape x , g ∘ position

open _⇒_


-- Linear/cartesian container morphism
record _⊸_ (C : Container s p) (C′ : Container s′ p′)
  : Type (s ⊔ p ⊔ s′ ⊔ p′) where
  field
    shape⊸    : Shape C → Shape C′
    position⊸ : ∀ {sh} → Position C′ (shape⊸ sh) ≃ Position C sh

  morphism : C ⇒ C′
  morphism .shape    = shape⊸
  morphism .position = position⊸ .fst

  ⟪_⟫⊸ : ⟦ C ⟧ X → ⟦ C′ ⟧ X
  ⟪_⟫⊸ = ⟪ morphism ⟫→

open _⊸_ using (shape⊸; position⊸; ⟪_⟫⊸)
