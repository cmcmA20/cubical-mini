{-# OPTIONS --safe #-}
module Meta.Show where

open import Foundations.Base
  renaming ( refl to reflₚ
           ; sym  to symₚ
           ; _∙_  to _∙ₚ_
           )
  renaming ( _∘ˢ_ to _∘ₜˢ_
           ; _∘_  to _∘ₜ_
           )

open import Meta.Literals.FromString

open import Correspondences.Binary.Reflexive
open import Correspondences.Binary.Transitive

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Reflection.Fixity
open import Data.Reflection.Name
open import Data.String.Base public
open import Data.String.Instances.Append

record ShowS : Type where
  constructor showS
  field unshowS : String → String

instance
  From-string-ShowS : From-string ShowS
  From-string-ShowS .From-string.Constraint _ = ⊤
  From-string-ShowS .from-string s = showS (s <>_)

  Reflᵘ-ShowS : Reflᵘ ShowS
  Reflᵘ-ShowS .mempty = showS id

  Transᵘ-ShowS : Transᵘ ShowS
  Transᵘ-ShowS ._<>_ (showS k₁) (showS k₂) = showS (k₁ ∘ˢ k₂)


record Show {ℓ} (T : Type ℓ) : Type ℓ where
  field
    shows-prec : Precedence → T → ShowS
    show       : T → String

open Show ⦃ ... ⦄ public

default-show : ∀ {ℓ} {A : Type ℓ} → (A → String) → Show A
default-show s .shows-prec _ x = from-string (s x)
default-show s .show = s

-- A common helper for implementing Show instances
show-parens : Bool → ShowS → ShowS
show-parens true  s = "(" <> s <> ")"
show-parens false s = s
