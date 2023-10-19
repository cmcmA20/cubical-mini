{-# OPTIONS --safe #-}
module Data.Nat.Properties where

open import Foundations.Base

open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Nat.Base public
open import Data.Nat.Path

-- addition

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

+-assoc-comm : (x y z : ℕ) → x + y + z ＝ x + z + y
+-assoc-comm x y z = sym (+-assoc x _ _) ∙ ap (λ q → x + q) (+-comm y z) ∙ +-assoc x _ _

-- multiplication

·-zeror : (x : ℕ) → x · zero ＝ zero
·-zeror  zero   = refl
·-zeror (suc x) = ·-zeror x

·-zero : (x y : ℕ) → x · y ＝ 0 → (x ＝ 0) ⊎ (y ＝ 0)
·-zero  zero    _      _   = inl refl
·-zero (suc _)  zero   _   = inr refl
·-zero (suc x) (suc y) prf = absurd (suc≠zero prf)

·-sucr : (x y : ℕ) → x · suc y ＝ x + x · y
·-sucr  zero   y = refl
·-sucr (suc x) y = ap suc (ap (λ z → y + z) (·-sucr x y) ∙ +-comm-assoc y x _)

·-comm : (x y : ℕ) → x · y ＝ y · x
·-comm  zero   y = sym (·-zeror y)
·-comm (suc x) y = ap (λ z → y + z) (·-comm x _) ∙ sym (·-sucr y x)

·-onel : (x : ℕ) → 1 · x ＝ x
·-onel = +-zeror

·-oner : (x : ℕ) → x · 1 ＝ x
·-oner x = ·-comm x 1 ∙ ·-onel x

·-distrib-+r : (x y z : ℕ) → (x + y) · z ＝ x · z + y · z
·-distrib-+r  zero   y z = refl
·-distrib-+r (suc x) y z = ap (λ q → z + q) (·-distrib-+r x y z) ∙ +-assoc z (x · z) (y · z)

·-distrib-+l : (x y z : ℕ) → x · (y + z) ＝ x · y + x · z
·-distrib-+l x y z = ·-comm x (y + z) ∙ ·-distrib-+r y z x ∙ ap² (_+_) (·-comm y x) (·-comm z x)

·-assoc : (x y z : ℕ) → x · (y · z) ＝ x · y · z
·-assoc  zero   y z = refl
·-assoc (suc x) y z = ap (λ q → y · z + q) (·-assoc x y z) ∙ sym (·-distrib-+r y _ _)

-- minimum

min-zerol : (x : ℕ) → min 0 x ＝ 0
min-zerol  zero   = refl
min-zerol (suc _) = refl

min-zeror : (x : ℕ) → min x 0 ＝ 0
min-zeror  zero   = refl
min-zeror (suc _) = refl

min-comm : (x y : ℕ) → min x y ＝ min y x
min-comm  zero    y      = min-zerol y ∙ sym (min-zeror y)
min-comm (suc _)  zero   = refl
min-comm (suc x) (suc y) = ap suc $ min-comm x y

min-assoc : (x y z : ℕ) → min x (min y z) ＝ min (min x y) z
min-assoc  zero    y       z      = min-zerol (min y z) ∙ sym (min-zerol z) ∙ ap (λ q → min q z) (sym $ min-zerol y)
min-assoc (suc x)  zero    z      = ap (min (suc x)) (min-zerol z) ∙ sym (min-zerol z)
min-assoc (suc x) (suc y)  zero   = refl
min-assoc (suc x) (suc y) (suc z) = ap suc $ min-assoc x y z

min-idem : (x : ℕ) → min x x ＝ x
min-idem  zero   = refl
min-idem (suc x) = ap suc $ min-idem x

-- maximum

max-zerol : (x : ℕ) → max 0 x ＝ x
max-zerol  zero   = refl
max-zerol (suc _) = refl

max-zeror : (x : ℕ) → max x 0 ＝ x
max-zeror  zero   = refl
max-zeror (suc _) = refl

max-comm : (x y : ℕ) → max x y ＝ max y x
max-comm  zero    y      = max-zerol y ∙ sym (max-zeror y)
max-comm (suc _)  zero   = refl
max-comm (suc x) (suc y) = ap suc $ max-comm x y

max-assoc : (x y z : ℕ) → max x (max y z) ＝ max (max x y) z
max-assoc  zero    y       z      = max-zerol (max y z) ∙ ap (λ q → max q z) (sym $ max-zerol y)
max-assoc (suc x)  zero    z      = ap (max (suc x)) (max-zerol z)
max-assoc (suc x) (suc y)  zero   = refl
max-assoc (suc x) (suc y) (suc z) = ap suc $ max-assoc x y z

max-idem : (x : ℕ) → max x x ＝ x
max-idem  zero   = refl
max-idem (suc x) = ap suc $ max-idem x
