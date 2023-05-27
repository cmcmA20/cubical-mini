{-# OPTIONS --safe #-}
open import Foundations.Base
module Foundations.Equiv.FromPath {ℓ} (P : (i : I) → Type ℓ) where

open import Foundations.Cubes.Base
open import Foundations.Equiv.Base

private
  ~P : (i : I) → Type ℓ
  ~P i = P (~ i)

  A B : Type ℓ
  A = P i0
  B = P i1

  f : A → B
  f x = coe0→1 P x

  g : B → A
  g y = coe1→0 P y

  u : ＜ id ／ (λ i → A → P i) ＼ f ＞
  u i x = coe0→i P i x

  v : ＜ g ／ (λ i → B → P i) ＼ id ＞
  v i y = coe1→i P i y

  has-fib : (y : B) → fibre f y
  has-fib y .fst = g y
  has-fib y .snd i = comp P (∂ i) λ where
    j (i = i1) → v j y
    j (i = i0) → u j (g y)
    j (j = i0) → g y

  fib-prop : (y : B) → is-prop (fibre f y)
  fib-prop y (x₀ , β₀) (x₁ , β₁) k = ω k , λ j → δ k (~ j) where
    square : ∀ (x : A) (β : f x ＝ y) j i → PartialP (∂ j ∨ ~ i) (λ _ → P (~ i))
    square x β j i (j = i0) = v (~ i) y
    square x β j i (j = i1) = u (~ i) x
    square x β j i (i = i0) = β (~ j)

    ω₀ : g y ＝ x₀
    ω₀ j = comp (λ i → P (~ i)) (∂ j) (square x₀ β₀ j)

    θ₀ : SquareP (λ i j → P (~ j)) (λ i → v (~ i) y) (λ i → u (~ i) x₀) (sym β₀) ω₀
    θ₀ j i = fill ~P (∂ j) i (square x₀ β₀ j)

    ω₁ : g y ＝ x₁
    ω₁ j = comp (λ i → P (~ i)) (∂ j) (square x₁ β₁ j)

    θ₁ : SquareP (λ i j → P (~ j)) (λ i → v (~ i) y) (λ i → u (~ i) x₁) (sym β₁) ω₁
    θ₁ j i = fill ~P (∂ j) i (square x₁ β₁ j)

    ω : x₀ ＝ x₁
    ω k = hcomp (∂ k) λ where
      j (k = i0) → ω₀ j
      j (k = i1) → ω₁ j
      j (j = i0) → g y

    θ : Square refl ω₀ ω ω₁
    θ k i = hfill (∂ k) i λ where
      j (k = i0) → ω₀ j
      j (k = i1) → ω₁ j
      j (j = i0) → g y

    δ : Square refl (sym β₀) (ap f ω) (sym β₁)
    δ k j = comp P (∂ j ∨ ∂ k) λ where
      i (i = i0) → θ k j
      i (j = i0) → v i y
      i (j = i1) → u i (ω k)
      i (k = i0) → θ₀ j (~ i)
      i (k = i1) → θ₁ j (~ i)

line→is-equiv : is-equiv f
line→is-equiv .equiv-proof y .fst = has-fib y
line→is-equiv .equiv-proof y .snd = fib-prop y _

line→equiv : A ≃ B
line→equiv .fst = f
line→equiv .snd = line→is-equiv
