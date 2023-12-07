{-# OPTIONS --safe #-}
module Data.Fin.Computational.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.ManifestBishop

open import Data.Nat.Base
open import Data.Fin.Computational.Path
open import Data.List.Base

private variable n : ℕ

instance
  fin-manifest-bishop-finite : Manifest-bishop-finite (Fin n)
  fin-manifest-bishop-finite = fin idₑ

  decomp-fin-fin : goal-decomposition (quote Manifest-bishop-finite) (Fin n)
  decomp-fin-fin = decomp (quote fin-manifest-bishop-finite) []
