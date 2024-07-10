{-# OPTIONS --safe #-}
module Data.Nat.Base where

open import Foundations.Base

open import Data.Empty.Base using (⊥)
open import Data.Unit.Base  using (⊤)

open import Agda.Builtin.Nat public
  using
    ( zero
    ; suc
    ; _+_
    ; _==_
    ; div-helper
    ; mod-helper )
  renaming
    ( Nat to ℕ
    ; _-_ to _∸_
    ; _*_ to _·_
    ; _<_ to infix 3 _<ᵇ_ )

private variable
  ℓ : Level
  A : Type ℓ

elim : (P : ℕ → Type ℓ)
     → P 0
     → ({n : ℕ} → P n → P (suc n))
     → (n : ℕ) → P n
elim P pz ps zero    = pz
elim P pz ps (suc n) = elim (P ∘ suc) (ps pz) ps n

rec : A → (A → A) → ℕ → A
rec z s = elim _ z s

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
min zero    _       = zero
min (suc x) zero    = zero
min (suc x) (suc y) = suc (min x y)

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

is-zero : ℕ → Type
is-zero 0       = ⊤
is-zero (suc _) = ⊥

is-positive : ℕ → Type
is-positive zero    = ⊥
is-positive (suc _) = ⊤
