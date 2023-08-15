{-# OPTIONS --safe #-}
module Data.Product.Base where

open import Foundations.Base

open import Data.Nat.Base

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ : Level
  n : ℕ
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ

Levelₓ : Level → Level → ℕ → Level
Levelₓ ℓ₁ ℓ₂ zero    = ℓ₂
Levelₓ ℓ₁ ℓ₂ (suc n) = ℓ₁ ⊔ (Levelₓ ℓ₁ ℓ₂ n)

functionₓ : (n : ℕ) → Type ℓ → Type ℓ′ → Type (Levelₓ ℓ ℓ′ n)
functionₓ zero    A B = B
functionₓ (suc n) A B = A → functionₓ n A B

_∘ⁿ_ : functionₓ 1 B C → functionₓ n A B → functionₓ n A C
_∘ⁿ_ {n = 0} f P = f P
_∘ⁿ_ {n = suc _} f P = λ x → f ∘ⁿ P x

Vecₓ : Type ℓ → ℕ → Type ℓ
Vecₓ A 0             = Lift _ ⊤
Vecₓ A 1             = A
Vecₓ A (suc (suc n)) = A × Vecₓ A (suc n)

-- rec
_$ₓ_ : functionₓ n A B → Vecₓ A n → B
_$ₓ_ {n = 0          } xs _ = xs
_$ₓ_ {n = 1          } xs   = xs
_$ₓ_ {n = suc (suc n)} f xs = f (xs .fst) $ₓ xs .snd

curryₓ : (Vecₓ A n → B) → functionₓ n A B
curryₓ {n = 0          } f   = f (lift tt)
curryₓ {n = 1          } f x = f x
curryₓ {n = suc (suc n)} f x = curryₓ λ xs → f (x , xs)

-- FIXME something wrong with termination checker
-- fun₁ : {n : ℕ} {A : Type ℓ} {B : Type ℓ′} (f : Vecₓ A n → B) → _$ₓ_ {A = A} (curryₓ f) ＝ f
-- fun₁ {n = 0          } f = fun-ext λ { (lift tt) → refl }
-- fun₁ {n = 1          } _ = refl
-- fun₁ {n = suc (suc n)} f = fun-ext helper
--   where
--   helper : _
--   helper (x , xs) = happly (fun₁ {n = suc n} {!!}) xs
