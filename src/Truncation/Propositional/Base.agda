{-# OPTIONS --safe #-}
module Truncation.Propositional.Base where

open import Foundations.Base

data ∥_∥₁ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₁    : A → ∥ A ∥₁
  squash₁ : (x y : ∥ A ∥₁) → x ＝ y

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

rec : is-prop B → (A → B) → ∥ A ∥₁ → B
rec B-prop f ∣ x ∣₁ = f x
rec B-prop f (squash₁ x y i) = B-prop (rec B-prop f x) (rec B-prop f y) i

∥-∥₁-is-prop : is-prop ∥ A ∥₁
∥-∥₁-is-prop = squash₁

map : (A → B) → (∥ A ∥₁ → ∥ B ∥₁)
map f = rec squash₁ (∣_∣₁ ∘ f)
