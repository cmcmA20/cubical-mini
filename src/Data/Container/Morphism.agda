{-# OPTIONS --safe #-}
module Data.Container.Morphism where

open import Foundations.Prelude

open import Data.Container.Base
open import Data.Container.Instances.Brackets

private variable
  ℓ ℓ′ s s′ p p′ : Level
  X  : Type ℓ

open Container

-- container morphism
record _⇒ᶜ_ (C : Container s p) (C′ : Container s′ p′)
            : Type (s ⊔ p ⊔ s′ ⊔ p′) where
  constructor _▶_
  field
    shape    : Shape C → Shape C′
    position : ∀ {sh} → Position C′ (shape sh) → Position C sh

  ⟪_⟫→ : ⟦ C ⟧ X → ⟦ C′ ⟧ X
  ⟪ x , g ⟫→ = shape x , g ∘ position

open _⇒ᶜ_

instance
  ⇒-Container : ⇒-notation (Container s p) (Container s′ p′) (Type (s ⊔ p ⊔ s′ ⊔ p′))
  ⇒-Container ._⇒_ = _⇒ᶜ_

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
