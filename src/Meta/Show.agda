{-# OPTIONS --safe #-}
module Meta.Show where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.String.Base public

record Show {ℓ} (T : Type ℓ) : Type ℓ where
  field
    shows-prec : ℕ → T → String
    -- ^ take care, nesting depth _increases_ in recursive calls

  show : T → String
  show = shows-prec 0

open Show ⦃ ... ⦄ public

-- A common helper for implementing Show instances
show-parens : Bool → String → String
show-parens true  s = "(" ++ₛ s ++ₛ ")"
show-parens false s = s

instance
  Show-Σ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
         → ⦃ Show A ⦄ → ⦃ ∀ {a} → Show (B a) ⦄ → Show (Σ[ a ꞉ A ] B a)
  Show-Σ .shows-prec n (a , b) = show-parens (0 <ᵇ n) $
    shows-prec (suc n) a ++ₛ " , " ++ₛ shows-prec n b
