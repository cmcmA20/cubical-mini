{-# OPTIONS --safe #-}
module Meta.Literals.FromNat where

open import Foundations.Base

open import Data.Fin.Inductive.Base -- TODO sure?
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

  From-ℕ-Type : ∀ {ℓ} → From-ℕ (Type ℓ)
  From-ℕ-Type .From-ℕ.Constraint _ = Lift _ ⊤
  From-ℕ-Type .from-ℕ n = Lift _ (Fin n)

  From-ℕ-Lift
    : ∀ {ℓ ℓ′} {A : Type ℓ}
    → ⦃ nl : From-ℕ A ⦄ → From-ℕ (Lift ℓ′ A)
  From-ℕ-Lift {ℓ′} ⦃ nl ⦄ .From-ℕ.Constraint n =
    Lift ℓ′ (nl .From-ℕ.Constraint n)
  From-ℕ-Lift ⦃ nl ⦄ .from-ℕ n ⦃ (c) ⦄ =
    lift (nl .from-ℕ n ⦃ c .lower ⦄)
