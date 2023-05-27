{-# OPTIONS --safe #-}
module Functions.Surjection where

open import Foundations.Base
open import Foundations.Equiv

open import Truncation.Propositional.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  f : A → B
  g : B → A

Split-Surjective : (A → B) → Type _
Split-Surjective f = Π[ y ꞉ _ ] (fibre f y)

_↠!_ : Type ℓ → Type ℓ′ → Type _
A ↠! B = Σ[ f ꞉ (A → B) ] Split-Surjective f


is-surjective : (A → B) → Type _
is-surjective f = Π[ y ꞉ _ ] ∥ fibre f y ∥₁

_↠_ : Type ℓ → Type ℓ′ → Type _
A ↠ B = Σ[ f ꞉ (A → B) ] is-surjective f

is-surjective-is-prop : is-prop (is-surjective f)
is-surjective-is-prop p q i y = squash₁ (p y) (q y) i

is-left-inverse-of→is-surjective : f is-left-inverse-of g → is-surjective f
is-left-inverse-of→is-surjective {g} s b = ∣ g b , s b ∣₁

is-equiv→is-surjective : is-equiv f → is-surjective f
is-equiv→is-surjective r y = ∣ equiv-proof r y .fst ∣₁
