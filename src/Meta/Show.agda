{-# OPTIONS --safe #-}
module Meta.Show where

open import Foundations.Base

open import Meta.Append
open import Meta.Literals.FromString
open import Meta.Reflection.Base
  using (Name; Precedence; show-name)

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.String.Base public
open import Data.String.Instances.Append

record ShowS : Type where
  constructor showS
  field unshowS : String → String

instance
  From-string-ShowS : From-string ShowS
  From-string-ShowS .From-string.Constraint _ = ⊤
  From-string-ShowS .from-string s = showS (s <>_)

  Append-ShowS : Append ShowS
  Append-ShowS .Append.mempty                     = showS id
  Append-ShowS .Append._<>_ (showS k₁) (showS k₂) = showS (k₁ ∘ k₂)


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


instance
  Show-Name : Show Name
  Show-Name = default-show show-name
