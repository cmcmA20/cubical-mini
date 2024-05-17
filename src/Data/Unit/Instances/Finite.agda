{-# OPTIONS --safe #-}
module Data.Unit.Instances.Finite where

open import Meta.Prelude

open import Combinatorics.Finiteness.Bishop.Manifest

open import Data.Fin.Computational.Closure
open import Data.Unit.Properties

instance
  ⊤-manifest-bishop-finite : Manifest-bishop-finite ⊤
  ⊤-manifest-bishop-finite = finite $ is-contr→equiv-⊤ fin-1-is-contr ⁻¹
  {-# OVERLAPPING ⊤-manifest-bishop-finite #-}
