{-# OPTIONS --safe #-}
module Data.Container.Instances.Brackets where

open import Foundations.Prelude

open import Data.Container.Base

instance
  ⟦⟧-container : {ℓ s p : Level} → ⟦⟧-notation (Container s p)
  ⟦⟧-container {ℓ} {s} {p} .⟦⟧-notation.lvl = ℓsuc (ℓ ⊔ s ⊔ p)
  ⟦⟧-container {ℓ} {s} {p} .⟦⟧-notation.Sem = Type ℓ → Type (ℓ ⊔ s ⊔ p)
  ⟦⟧-container .⟦_⟧ (S ▶ P) X = Σ[ s ꞉ S ] (P s → X)
