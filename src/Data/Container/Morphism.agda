{-# OPTIONS --safe #-}
module Data.Container.Morphism where

open import Foundations.Prelude

open import Data.Container.Base

private variable s s′ p p′ : Level

open Container

-- container morphism
record _⇒ᶜ_ (C : Container s p) (C′ : Container s′ p′)
            : Type (s ⊔ p ⊔ s′ ⊔ p′) where
  inductive
  eta-equality
  constructor _▶_
  field
    map-shape    : Shape C → Shape C′
    map-position : ∀ {sh} → Position C′ (map-shape sh) → Position C sh

open _⇒ᶜ_

instance
  ⇒-Container : ⇒-notation (Container s p) (Container s′ p′) (Type (s ⊔ p ⊔ s′ ⊔ p′))
  ⇒-Container .⇒-notation.Constraint _ _ = ⊤ₜ
  ⇒-Container ._⇒_ c d = c ⇒ᶜ d

  ⇒-Container-exp : ⇒-notation (Container s p) (Container s′ p′) (Container (s ⊔ s′) (s ⊔ p ⊔ p′))
  ⇒-Container-exp .⇒-notation.Constraint _ _ = ⊤ₜ
  ⇒-Container-exp .⇒-notation._⇒_ (S ▶ P) (S′ ▶ P′) = (S → S′) ▶ (λ f → ∀ {sh} → P′ (f sh) → P sh)

-- Linear/cartesian container morphism
_⊸_ : (C : Container s p) (C′ : Container s′ p′) → Type (s ⊔ p ⊔ s′ ⊔ p′)
C ⊸ C′ = Σ[ f ꞉ C ⇒ᶜ C′ ] Π[ sh ꞉ C .Shape ] is-equiv (f .map-position {sh})
