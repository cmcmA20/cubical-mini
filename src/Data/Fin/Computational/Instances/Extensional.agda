{-# OPTIONS --safe #-}
module Data.Fin.Computational.Instances.Extensional where

open import Foundations.Base

open import Meta.Extensionality

open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Path

Extensional-Fin : ∀ {@0 n} → Extensional (Fin n) 0ℓ
Extensional-Fin .Pathᵉ (mk-fin u) (mk-fin v) = u ＝ v
Extensional-Fin .reflᵉ _ = refl
Extensional-Fin .idsᵉ .to-path = fin-ext
Extensional-Fin .idsᵉ .to-path-over p i j = p (i ∧ j)

instance
  extensionality-fin : ∀ {@0 n} → Extensionality (Fin n)
  extensionality-fin .Extensionality.lemma = quote Extensional-Fin
