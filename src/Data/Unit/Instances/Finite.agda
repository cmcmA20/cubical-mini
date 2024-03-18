{-# OPTIONS --safe #-}
module Data.Unit.Instances.Finite where

open import Meta.Prelude

open import Meta.Search.Finite.ManifestBishop

open import Data.Fin.Computational.Closure
open import Data.List.Base
open import Data.Unit.Properties

instance
  ⊤-manifest-bishop-finite : Manifest-bishop-finite ⊤
  ⊤-manifest-bishop-finite = fin $ is-contr→equiv-⊤ fin-1-is-contr ⁻¹

  decomp-fin-⊤ : goal-decomposition (quote Manifest-bishop-finite) ⊤
  decomp-fin-⊤ = decomp (quote ⊤-manifest-bishop-finite) []
