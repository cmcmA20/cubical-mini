{-# OPTIONS --safe #-}
module Meta.Literals.FromNeg where

open import Foundations.Base

open import Agda.Builtin.FromNeg public
  using ()
  renaming ( Negative to From-neg
           ; fromNeg to from-neg )

instance
  From-neg-Lift
    : ∀ {ℓ ℓ′} {A : Type ℓ}
    → ⦃ nl : From-neg A ⦄ → From-neg (Lift ℓ′ A)
  From-neg-Lift {ℓ′} ⦃ nl ⦄ .From-neg.Constraint n =
    Lift ℓ′ (nl .From-neg.Constraint n)
  From-neg-Lift ⦃ nl ⦄ .From-neg.fromNeg n ⦃ (c) ⦄ =
    lift (nl .from-neg n ⦃ c .lower ⦄)
