{-# OPTIONS --safe #-}
module Data.Bool.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.ManifestBishop

open import Data.Bool.Base
open import Data.Fin.Computational.Base
open import Data.List.Base

instance
  bool-manifest-bishop-finite : Manifest-bishop-finite Bool
  bool-manifest-bishop-finite = fin $ iso→equiv go where
    go : Bool ≅ Fin 2
    go .fst false = fzero
    go .fst true = fsuc fzero
    go .snd .is-iso.inv (mk-fin 0) = false
    go .snd .is-iso.inv (mk-fin 1) = true
    go .snd .is-iso.rinv (mk-fin 0) = refl
    go .snd .is-iso.rinv (mk-fin 1) = refl
    go .snd .is-iso.linv false = refl
    go .snd .is-iso.linv true = refl

  decomp-fin-bool : goal-decomposition (quote Manifest-bishop-finite) Bool
  decomp-fin-bool = decomp (quote bool-manifest-bishop-finite) []
