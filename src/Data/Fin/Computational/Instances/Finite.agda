{-# OPTIONS --safe #-}
module Data.Fin.Computational.Instances.Finite where

open import Meta.Prelude

open import Combinatorics.Finiteness.Bishop.Manifest

open import Data.Fin.Computational.Base

private variable n : ℕ

instance
  fin-manifest-bishop-finite : Manifest-bishop-finite (Fin n)
  fin-manifest-bishop-finite = finite refl
  {-# OVERLAPPING fin-manifest-bishop-finite #-}
