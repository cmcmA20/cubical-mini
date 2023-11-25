{-# OPTIONS --safe #-}
module Meta.Ord where

open import Foundations.Base

open import Meta.Search.Discrete
open import Meta.Search.HLevel

open import Order.Linear

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Sum.Base

open import Truncation.Propositional.Base


data Tri {ℓo} {ℓ} {T : Type ℓ} (_<_ : T → T → Type ℓo) (x y : T) : Type (ℓ ⊔ ℓo) where
  lt : (x<y :   x < y) (x≠y : ¬ x ＝ y) (y≮x : ¬ y < x) → Tri _<_ x y
  eq : (x≮y : ¬ x < y) (x=y :   x ＝ y) (y≮x : ¬ y < x) → Tri _<_ x y
  gt : (x≮y : ¬ x < y) (x≠y : ¬ x ＝ y) (y<x :   y < x) → Tri _<_ x y

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
  ℓ : Level
  T : Type ℓ

ord→is-linear-order : ⦃ ord : Ord T ⦄ → is-linear-order _<_
ord→is-linear-order ⦃ ord ⦄ .is-linear-order.<-thin = ord .<-thin
ord→is-linear-order .is-linear-order.<-asym {x} {y} p q with x ≤? y
... | lt x<y x≠y y≮x = y≮x q
... | eq x≮y x=y y≮x = y≮x q
... | gt x≮y x≠y y<x = x≮y p
ord→is-linear-order .is-linear-order.<-cmp {x} {y} x<z with x ≤? y
... | lt x<y x≠y y≮x = ∣ inl x<y ∣₁
ord→is-linear-order .is-linear-order.<-cmp {x} {y} {z} x<z | eq x≮y x=y y≮x with y ≤? z
... | lt y<z y≠z z≮y = ∣ inr y<z ∣₁
... | eq y≮z y=z z≮y = ⊥.rec (y≮z (subst (_< z) x=y x<z))
... | gt y≮z y≠z z<y = ∣ inr (subst (_< z) x=y x<z) ∣₁
ord→is-linear-order ⦃ ord ⦄  .is-linear-order.<-cmp {x} {y} {z} x<z | gt x≮y x≠y y<x with y ≤? z
... | lt y<z y≠z z≮y = ∣ inr y<z ∣₁
... | eq y≮z y=z z≮y = ⊥.rec (x≮y (subst (x <_) (sym y=z) x<z))
... | gt y≮z y≠z z<y = ⊥.rec (y≮z (ord .<-trans y<x x<z))
ord→is-linear-order .is-linear-order.<-conn {x} {y} y≮x x≮y with x ≤? y
... | lt x<y  x≠y y≮′x = ⊥.rec (y≮x x<y)
... | eq x≮′y x=y y≮′x = x=y
... | gt x≮′y x≠y y<x  = ⊥.rec (x≮y y<x)

instance
  ord→is-discrete : ⦃ ord : Ord T ⦄ → is-discrete T
  ord→is-discrete .is-discrete-β x y with x ≤? y
  ... | lt _ x≠y _ = no  x≠y
  ... | eq _ x=y _ = yes x=y
  ... | gt _ x≠y _ = no  x≠y
