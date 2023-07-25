{-# OPTIONS --safe #-}
module Functions.Constant where

open import Foundations.Base

open import Meta.Search.HLevel

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

2-Constant : (A → B) → Type _
2-Constant f = ∀ x y → f x ＝ f y

is-set→2-Constant-is-prop : is-set B → (f : A → B) → is-prop (2-Constant f)
is-set→2-Constant-is-prop B-set _ = hlevel! where instance _ = B-set
