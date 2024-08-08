{-# OPTIONS --safe #-}
module Data.Nat.Order.Minmax where

open import Meta.Prelude

open import Data.Bool as Bool
open import Data.Reflects.Base
open import Data.Nat.Base
open import Data.Nat.Order.Inductive.Base using (_≤?_)
open import Data.Nat.Order.Base
open import Data.Nat.Properties

min-if : ∀ {x y} → min x y ＝ (if x ≤? y then x else y)
min-if {x = zero}              = refl
min-if {x = suc x} {y = zero}  = refl
min-if {x = suc x} {y = suc y} =
    ap suc (min-if {x = x} {y = y})
  ∙ Bool.elim {P = λ q → suc (if q then x else y) ＝ (if q then suc x else suc y)}
              refl refl (x ≤? y)

max-if : ∀ {x y} → max x y ＝ (if x ≤? y then y else x)
max-if {x = zero}  {y = zero}  = refl
max-if {x = zero}  {y = suc y} = refl
max-if {x = suc x} {y = zero}  = refl
max-if {x = suc x} {y = suc y} =
    ap suc (max-if {x = x} {y = y})
  ∙ Bool.elim {P = λ q → suc (if q then y else x) ＝ (if q then suc y else suc x)}
              refl refl (x ≤? y)

min-+-l : ∀ {x y} → min x (x + y) ＝ x
min-+-l {x} {y}  = min-if ∙ subst (λ q → (if q then x else x + y) ＝ x) ((is-true≃is-trueₚ $ reflects-true (≤-reflects x (x + y)) ≤-+-r) ⁻¹) refl

min-l : ∀ {x y} → is-true (min x y ≤? x)
min-l {x = zero}              = tt
min-l {x = suc x} {y = zero}  = tt
min-l {x = suc x} {y = suc y} = min-l {x = x} {y = y}

min-r : ∀ {x y} → is-true (min x y ≤? y)
min-r {x = zero}              = tt
min-r {x = suc x} {y = zero}  = tt
min-r {x = suc x} {y = suc y} = min-r {x = x} {y = y}

max-l : ∀ {x y} → is-true (x ≤? max x y)
max-l {x = zero}  {y = zero}  = tt
max-l {x = zero}  {y = suc y} = tt
max-l {x = suc x} {y = zero}  = reflects-true (≤-reflects x x) ≤-refl
max-l {x = suc x} {y = suc y} = max-l {x = x} {y = y}

max-r : ∀ {x y} → is-true (y ≤? max x y)
max-r {x = zero}  {y = zero}  = tt
max-r {x = zero}  {y = suc y} = reflects-true (≤-reflects y y) ≤-refl
max-r {x = suc x} {y = zero}  = tt
max-r {x = suc x} {y = suc y} = max-r {x = x} {y = y}

≤ᵇ-min : ∀ {x y z} → (x ≤? min y z) ＝ (x ≤? y) and (x ≤? z)
≤ᵇ-min {x = zero}  {y = zero}              = refl
≤ᵇ-min {x = suc x} {y = zero}              = refl
≤ᵇ-min {x = zero}  {y = suc y} {z = zero}  = refl
≤ᵇ-min {x = suc x} {y = suc y} {z = zero}  = and-absorb-r (x <? suc y) ⁻¹
≤ᵇ-min {x = zero}  {y = suc y} {z = suc z} = refl
≤ᵇ-min {x = suc x} {y = suc y} {z = suc z} = ≤ᵇ-min {x = x} {y = y} {z = z}
