{-# OPTIONS --safe #-}
module Meta.Literals.FromNat where

open import Data.Nat.Base
open import Data.Unit.Base

open import Agda.Builtin.FromNat public
  using ()
  renaming ( Number to From-ℕ
           ; fromNat to from-ℕ )

instance
  From-ℕ-ℕ : From-ℕ ℕ
  From-ℕ-ℕ .From-ℕ.Constraint _ = ⊤
  From-ℕ-ℕ .from-ℕ n = n
