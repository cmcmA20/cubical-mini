{-# OPTIONS --safe #-}
module Data.Fin.Instances.Finite where

open import Foundations.Base

open import Correspondences.Finite.ManifestBishop

open import Data.Empty.Instances.Finite
open import Data.Fin.Base
open import Data.Maybe.Instances.Finite
open import Data.Nat.Base

private variable n : ℕ

instance
  fin-manifest-bishop-finite : Manifest-bishop-finite (Fin n)
  fin-manifest-bishop-finite {0}     = ⊥-manifest-bishop-finite
  fin-manifest-bishop-finite {suc _} = maybe-manifest-bishop-finite ⦃ fin-manifest-bishop-finite ⦄
