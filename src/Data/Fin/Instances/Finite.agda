{-# OPTIONS --safe #-}
module Data.Fin.Instances.Finite where

open import Foundations.Base

open import Meta.Search.Finite.Bishop

open import Data.Empty.Instances.Finite
open import Data.Fin.Base
open import Data.Maybe.Instances.Finite
open import Data.Nat.Base

private variable n : ℕ

instance
  fin-is-bishop-finite : is-bishop-finite (Fin n)
  fin-is-bishop-finite {0}     = ⊥-is-bishop-finite
  fin-is-bishop-finite {suc _} = maybe-is-bishop-finite fin-is-bishop-finite

  decomp-fin-fin : goal-decomposition (quote is-bishop-finite) (Fin n)
  decomp-fin-fin = decomp (quote fin-is-bishop-finite) []
