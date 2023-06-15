{-# OPTIONS --safe #-}
module Meta.Literals.FromNat where

open import Data.Nat.Base
open import Data.Unit.Base

open import Agda.Builtin.FromNat public
  using ( Number )
  renaming ( fromNat to from-ℕ )

instance
  Number-ℕ : Number ℕ
  Number-ℕ .Number.Constraint _ = ⊤
  Number-ℕ .Number.fromNat n = n
