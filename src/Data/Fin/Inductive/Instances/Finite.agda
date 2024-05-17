{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Instances.Finite where

open import Meta.Prelude

open import Combinatorics.Finiteness.Bishop.Manifest

open import Data.Fin.Computational.Base
  using (default≃computational)
open import Data.Fin.Inductive.Base

private variable n : ℕ

instance
  fin-manifest-bishop-finite : Manifest-bishop-finite (Fin n)
  fin-manifest-bishop-finite = finite $ default≃inductive ⁻¹ ∙ default≃computational
  {-# OVERLAPPING fin-manifest-bishop-finite #-}
