{-# OPTIONS --safe #-}
module Data.Bool.Instances.Finite where

open import Foundations.Base

open import Meta.Finite

open import Data.Bool.Base
open import Data.Fin.Base

open import Truncation.Propositional.Base

instance
  Finite-Bool : Finite Bool
  Finite-Bool .Finite.cardinality = 2
  Finite-Bool .Finite.enumeration = ∣ iso→equiv 𝔯 ∣₁ where
    𝔯 : Iso _ _
    𝔯 .fst false = fzero
    𝔯 .fst true  = fsuc fzero
    𝔯 .snd .is-iso.inv fzero    = false
    𝔯 .snd .is-iso.inv (fsuc _) = true
    𝔯 .snd .is-iso.rinv fzero        = refl
    𝔯 .snd .is-iso.rinv (fsuc fzero) = refl
    𝔯 .snd .is-iso.linv false = refl
    𝔯 .snd .is-iso.linv true  = refl
