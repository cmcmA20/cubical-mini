{-# OPTIONS --safe #-}
module Meta.Ord where

open import Foundations.Base

open import Meta.Search.Discrete
open import Meta.Search.HLevel

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

instance
  ord→is-discrete : ⦃ ord : Ord T ⦄ → is-discrete T
  ord→is-discrete .is-discrete-β x y with x ≤? y
  ... | lt _ x≠y _ = no  x≠y
  ... | eq _ x=y _ = yes x=y
  ... | gt _ x≠y _ = no  x≠y
