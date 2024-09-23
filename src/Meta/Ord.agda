{-# OPTIONS --safe #-}
module Meta.Ord where

open import Meta.Prelude

open import Logic.Discreteness

open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Truncation.Propositional.Base as ∥-∥₁
open import Data.Tri.Base

record Ord {ℓ} (T : Type ℓ) : Typeω where
  no-eta-equality
  field
    ℓo      : Level
    _<_     : T → T → Type ℓo
    <-thin  : ∀ {x y} → is-prop (x < y)
    <-trans : ∀ {x y z} → x < y → y < z → x < z
    _≤?_    : (x y : T) → Tri _<_ x y

open Ord ⦃ ... ⦄
  using (_<_; _≤?_)
  public

open Ord using (<-thin; <-trans)

private variable
  ℓ ℓ′ : Level
  T : Type ℓ
  S : Type ℓ′

instance
  ord→is-discrete : ⦃ ord : Ord T ⦄ → is-discrete T
  ord→is-discrete {x} {y} with x ≤? y
  ... | lt _ x≠y _ = no  x≠y
  ... | eq _ x=y _ = yes x=y
  ... | gt _ x≠y _ = no  x≠y
  {-# OVERLAPPABLE ord→is-discrete #-}

≃→ord : T ≃ S → Ord S → Ord T
≃→ord e o .Ord.ℓo = o .Ord.ℓo
≃→ord e o .Ord._<_ x y = o .Ord._<_ (e $ x) (e $ y)
≃→ord e o .<-thin = o .<-thin
≃→ord e o .<-trans = o .<-trans
≃→ord e o .Ord._≤?_ x y = Tri-elim
  {C = λ _ → Tri (≃→ord e o .Ord._<_) _ _}
  (λ x<y x≠y y≮x → lt x<y (λ x=y → x≠y (ap$ e x=y)) y≮x)
  (λ x≮y x=y y≮x → eq x≮y (Equiv.injective e x=y) y≮x)
  (λ x≮y x≠y y<x → gt x≮y (λ x=y → x≠y (ap$ e x=y)) y<x)
  (o .Ord._≤?_ (e $ x) (e $ y))
