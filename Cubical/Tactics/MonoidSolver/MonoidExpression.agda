{-# OPTIONS --safe #-}
module Cubical.Tactics.MonoidSolver.MonoidExpression where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.Vec.Base

open import Cubical.Algebra.CommMonoid.Base

private
  variable
    ℓ : Level

infixl 7 _⊗_

-- Expression in a type M with n variables
data Expr (M : Type ℓ) (n : ℕ) : Type ℓ where
  ∣   : Fin n → Expr M n
  ε⊗  : Expr M n
  _⊗_ : Expr M n → Expr M n → Expr M n
