module Data.String.Properties.Unsafe where

open import Foundations.Base

open import Data.String.Base public
open import Data.String.Operations
open import Data.List.Base
open import Data.Nat.Base
open import Data.Maybe.Base as Maybe

postulate
  string→list-++ₛ : {s₁ s₂ : String} → string→list (s₁ ++ₛ s₂) ＝ string→list s₁ ++ string→list s₂

  length-tail : {s : String} → lengthₛ s ＝ Maybe.rec zero (suc ∘ lengthₛ) (tailₛ s)
