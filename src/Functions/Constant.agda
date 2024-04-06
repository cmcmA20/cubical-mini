{-# OPTIONS --safe #-}
module Functions.Constant where

open import Foundations.Base

open import Structures.n-Type

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

Constant : (A → B) → Type _
Constant {A} {B} f = Σ[ b ꞉ B ] Π[ a ꞉ A ] (f a ＝ b)

2-Constant : (A → B) → Type _
2-Constant f = ∀ x y → f x ＝ f y

is-set→2-Constant-is-prop : is-set B → (f : A → B) → is-prop (2-Constant f)
is-set→2-Constant-is-prop B-set _ = hlevel! where instance _ = hlevel-basic-instance 2 B-set
