{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Show where

open import Foundations.Base

open import Meta.Deriving.Show

open import Data.Tree.Binary.Base

instance unquoteDecl Show-Tree = derive-show Show-Tree (quote Tree)

private module _ where
  open import Data.Nat.Instances.Show

  _ : show (node empty (leaf 17)) ＝ "node empty (leaf 17)"
  _ = refl
