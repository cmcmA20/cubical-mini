{-# OPTIONS --safe #-}
module Data.Container.Instances.Brackets where

open import Foundations.Prelude

open import Data.Container.Base
open import Data.Container.Morphism

private variable ℓ s s′ p p′ : Level

instance
  ⟦⟧-container : ∀ {ℓ} → ⟦⟧-notation (Container s p)
  ⟦⟧-container {s} {p} {ℓ} .⟦⟧-notation.lvl = ℓsuc (ℓ ⊔ s ⊔ p)
  ⟦⟧-container {s} {p} {ℓ} .⟦⟧-notation.Sem = Type ℓ → Type (ℓ ⊔ s ⊔ p)
  ⟦⟧-container .⟦_⟧ (S ▶ P) X = Σ[ s ꞉ S ] (P s → X)

  ⟦⟧-container-morphism
    : ∀ {ℓ} {C : Container s p} {C′ : Container s′ p′}
    → ⟦⟧-notation (C ⇒ᶜ C′)
  ⟦⟧-container-morphism .⟦⟧-notation.lvl = _
  ⟦⟧-container-morphism {ℓ} {C} {C′} .⟦⟧-notation.Sem =
    {X : Type ℓ} → ⟦ C ⟧ X → ⟦ C′ ⟧ X
  ⟦⟧-container-morphism .⟦⟧-notation.⟦_⟧ (f ▶ g) = bimap f (_∘ g)
