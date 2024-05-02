{-# OPTIONS --safe #-}
module Data.Empty.Instances.Finite where

open import Meta.Prelude

open import Combinatorics.Finiteness.ManifestBishop

open import Data.Empty.Base
open import Data.Fin.Computational.Closure

instance
  ⊥-manifest-bishop-finite : Manifest-bishop-finite ⊥
  ⊥-manifest-bishop-finite = fin $ fin-0-is-initial ⁻¹
