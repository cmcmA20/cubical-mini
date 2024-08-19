{-# OPTIONS --safe #-}
module Data.Sum.Exclusive.Instances.Show where

open import Foundations.Base

open import Meta.Deriving.Show

open import Data.Empty.Base
open import Data.Empty.Instances.Show
open import Data.Nat.Base
open import Data.Sum.Exclusive.Base

instance
  unquoteDecl Show-⊻ = derive-show Show-⊻ (quote _⊻ₜ_)

private module _ where
  open import Data.Nat.Instances.Show

  _ : show (the (ℕ ⊻ ⊥) (inxl 0 id)) ＝ "inxl 0 <↯>"
  _ = refl

  _ : show (the ((⊥ ⊻ ℕ) ⊻ ⊥) (inxl (inxr 0 id) id)) ＝ "inxl (inxr 0 <↯>) <↯>"
  _ = refl
