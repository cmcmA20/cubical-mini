{-# OPTIONS --safe #-}
module Data.Fin.Instances.Discrete where

open import Foundations.Base

open import Logic.Discreteness

open import Data.Dec.Base as Dec
open import Data.Nat.Base

open import Data.Fin.Base
open import Data.Fin.Path

private variable n : ℕ

instance
  fin-is-discrete : is-discrete (Fin n)
  fin-is-discrete {suc _} {(fzero)} {(fzero)} = yes refl
  fin-is-discrete {suc _} {(fzero)} {fsuc l}  = no fzero≠fsuc
  fin-is-discrete {suc _} {fsuc k}  {(fzero)} = no fsuc≠fzero
  fin-is-discrete {suc _} {fsuc k}  {fsuc l}  =
    Dec.dmap (ap fsuc) (_∘ fsuc-inj) (fin-is-discrete {_} {k} {l})
