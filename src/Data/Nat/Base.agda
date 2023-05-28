{-# OPTIONS --safe #-}
module Data.Nat.Base where

open import Foundations.Base

open import Agda.Builtin.Nat public
  using
    ( zero
    ; suc
    ; _+_
    ; _-_
    ; _==_
    ; div-helper
    ; mod-helper )
  renaming
    ( Nat to ℕ
    ; _*_ to _·_
    ; _<_ to _<-internal_ )

private variable
  ℓ : Level
  A : Type ℓ

elim : (P : ℕ → Type ℓ)
     → P 0
     → ({n : ℕ} → P n → P (suc n))
     → (n : ℕ) → P n
elim P pz ps zero    = pz
elim P pz ps (suc n) = elim (λ z → P (suc z)) (ps pz) ps n

iter : ℕ → (A → A) → A → A
iter zero    f = id
iter (suc n) f = f ∘ iter n f

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero  = 1
x ^ suc y = x · (x ^ y)

max : ℕ → ℕ → ℕ
max zero    zero    = zero
max zero    (suc y) = suc y
max (suc x) zero    = suc x
max (suc x) (suc y) = suc (max x y)

min : ℕ → ℕ → ℕ
min zero    zero    = zero
min zero    (suc y) = zero
min (suc x) zero    = zero
min (suc x) (suc y) = suc (min x y)

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n
