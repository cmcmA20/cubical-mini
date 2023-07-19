{-# OPTIONS --safe #-}
module Data.Nat.Properties where

open import Foundations.Base

open import Data.Dec.Base
open import Data.Id

open import Data.Nat.Base public
open import Data.Nat.Path

+-zeror : (x : ℕ) → x + 0 ＝ x
+-zeror zero    = refl
+-zeror (suc x) = ap suc (+-zeror x)

+-sucr : (x y : ℕ) → x + suc y ＝ suc (x + y)
+-sucr zero y    = refl
+-sucr (suc x) y = ap suc (+-sucr x y)

+-comm : (x y : ℕ) → x + y ＝ y + x
+-comm zero y = sym (+-zeror y)
+-comm (suc x) y = ap suc (+-comm x y) ∙ sym (+-sucr y x)

+-assoc : (x y z : ℕ) → x + (y + z) ＝ x + y + z
+-assoc zero    y z = refl
+-assoc (suc x) y z = ap suc (+-assoc x _ _)

+-inj-l : (x y z : ℕ) → x + y ＝ x + z → y ＝ z
+-inj-l  zero   y z prf = prf
+-inj-l (suc x) y z prf = +-inj-l _ _ _ (suc-inj prf)

+-inj-r : (x y z : ℕ) → x + z ＝ y + z → x ＝ y
+-inj-r x y z prf = +-inj-l _ _ _ (+-comm z x ∙ prf ∙ +-comm y z)

+-comm-assoc : (x y z : ℕ) → x + (y + z) ＝ y + (x + z)
+-comm-assoc x y z = +-assoc x y _
                   ∙ ap (λ q → q + z) (+-comm x y)
                   ∙ sym (+-assoc y x _)

·-zeror : (x : ℕ) → x · zero ＝ zero
·-zeror  zero   = refl
·-zeror (suc x) = ·-zeror x

·-sucr : (x y : ℕ) → x · suc y ＝ x + x · y
·-sucr  zero   y = refl
·-sucr (suc x) y = ap suc (ap (λ z → y + z) (·-sucr x y) ∙ +-comm-assoc y x _)

·-comm : (x y : ℕ) → x · y ＝ y · x
·-comm  zero   y = sym (·-zeror y)
·-comm (suc x) y = ap (λ z → y + z) (·-comm x _) ∙ sym (·-sucr y x)

·-distrib-+r : (x y z : ℕ) → (x + y) · z ＝ x · z + y · z
·-distrib-+r  zero   y z = refl
·-distrib-+r (suc x) y z = ap (λ q → z + q) (·-distrib-+r x y z) ∙ +-assoc z (x · z) (y · z)

·-distrib-+l : (x y z : ℕ) → x · (y + z) ＝ x · y + x · z
·-distrib-+l x y z = ·-comm x (y + z) ∙ ·-distrib-+r y z x ∙ ap₂ (_+_) (·-comm y x) (·-comm z x)

·-assoc : (x y z : ℕ) → x · (y · z) ＝ x · y · z
·-assoc  zero   y z = refl
·-assoc (suc x) y z = ap (λ q → y · z + q) (·-assoc x y z) ∙ sym (·-distrib-+r y _ _)

-- TODO
