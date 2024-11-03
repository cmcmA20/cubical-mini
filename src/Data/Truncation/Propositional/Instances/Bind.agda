{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Instances.Bind where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Base
open import Meta.Effect.Bind
open import Meta.Effect.Idiom
open import Meta.Inductive

open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Instances.Idiom public

private variable
  n : HLevel
  ℓ : Level
  A : Type ℓ

instance
  private
    _ : H-Level (suc n) ∥ A ∥₁
    _ = hlevel-prop-instance squash₁

  Bind-∥-∥₁ : Bind (eff ∥_∥₁)
  Bind-∥-∥₁ ._>>=_ = flip rec!

  Lawful-Bind-∥-∥₁ : Lawful-Bind (eff ∥_∥₁)
  Lawful-Bind-∥-∥₁ .Lawful-Bind.>>=-id-l = refl
  Lawful-Bind-∥-∥₁ .Lawful-Bind.>>=-id-r {A} {mx} = go mx where opaque
    go : (x : ∥ A ∥₁) → (x >>= pure) ＝ x
    go = elim! λ _ → refl
  Lawful-Bind-∥-∥₁ .Lawful-Bind.>>=-assoc {A} {mx} {f} {g} = go mx where opaque
    go : (x : ∥ A ∥₁) → (x >>= f >>= g) ＝ (x >>= λ x → f x >>= g)
    go = elim! λ _ → refl
