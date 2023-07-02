{-# OPTIONS --safe #-}
module Data.Bool.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.Bool.Base
open import Data.Fin.Base

open import Truncation.Propositional.Base

instance
  bool-is-fin-set : is-fin-set Bool
  bool-is-fin-set = fin ∣ iso→equiv go ∣₁ where
    go : Iso Bool (Fin 2)
    go .fst false = fzero
    go .fst true  = fsuc fzero
    go .snd .is-iso.inv fzero    = false
    go .snd .is-iso.inv (fsuc _) = true
    go .snd .is-iso.rinv fzero        = refl
    go .snd .is-iso.rinv (fsuc fzero) = refl
    go .snd .is-iso.linv false = refl
    go .snd .is-iso.linv true  = refl
