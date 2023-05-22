{-# OPTIONS --safe #-}
module Data.Product.Dependent where

open import Foundations.Base

open import Data.Nat.Base

open import Data.Product.Base

private variable
  ℓ ℓ′ : Level
  n : ℕ
  A : Type ℓ
  B : Vecₓ A n → Type ℓ′

Πₓ : (n : ℕ) → (A : Type ℓ) → (Vecₓ A n → Type ℓ′) → Type (Levelₓ ℓ ℓ′ n)
Πₓ 0             _ B = B (lift tt)
Πₓ 1             A B = Π[ a ꞉ A ] B a
Πₓ (suc (suc n)) A B = Π[ a ꞉ A ] Πₓ (suc n) A (λ as → B (a , as))

_$ⁿ_ : {A : Type ℓ} {B : Vecₓ A n → Type ℓ′} → Πₓ n A B → (xs : Vecₓ A n) → B xs
_$ⁿ_ {n = 0} f _  = f
_$ⁿ_ {n = 1} f xs = f xs
_$ⁿ_ {n = suc (suc n)} {A} f (x , xs) = _$ⁿ_ {A = A} (f x) xs
