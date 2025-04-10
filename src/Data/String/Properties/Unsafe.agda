module Data.String.Properties.Unsafe where

open import Foundations.Base

open import Data.String.Base public
open import Data.List.Base

postulate
  string→list-++ₛ : {s₁ s₂ : String} → string→list (s₁ ++ₛ s₂) ＝ string→list s₁ ++ string→list s₂
