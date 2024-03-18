{-# OPTIONS --safe #-}
module Data.Fin.Computational.Instances.Finite where

open import Meta.Prelude

open import Meta.Search.Finite.ManifestBishop

open import Data.Nat.Base
open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Path
open import Data.List.Base

private variable n : ℕ

instance
  fin-manifest-bishop-finite : Manifest-bishop-finite (Fin n)
  fin-manifest-bishop-finite = fin refl

  decomp-fin-fin : goal-decomposition (quote Manifest-bishop-finite) (Fin n)
  decomp-fin-fin = decomp (quote fin-manifest-bishop-finite) []
