{-# OPTIONS --safe #-}
module Data.Container.Instances.Brackets where

open import Foundations.Prelude

open import Meta.Brackets

open import Data.Container.Base

instance
  Sem-container : {ℓ s p : Level} → ⟦⟧-notation (Container s p)
  Sem-container {ℓ} {s} {p} .⟦⟧-notation.lvl = ℓsuc (ℓ ⊔ s ⊔ p)
  Sem-container {ℓ} {s} {p} .⟦⟧-notation.Sem = Type ℓ → Type (ℓ ⊔ s ⊔ p)
  Sem-container .⟦⟧-notation.⟦_⟧ (S ▶ P) X = Σ[ s ꞉ S ] (P s → X)
