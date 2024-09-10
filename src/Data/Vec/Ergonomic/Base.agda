{-# OPTIONS --safe #-}
module Data.Vec.Ergonomic.Base where

open import Foundations.Base

open import Data.Nat.Base
  using (ℕ; zero; suc)
  public
open import Data.Unit.Base
open import Data.Vec.Interface

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

Vec : Type ℓ → (n : ℕ) → Type ℓ
Vec _ 0 = ⊤
Vec A 1 = A
Vec A (suc (suc n)) = A × Vec A (suc n)

infixr 5 _∷_
_∷_ : ∀{n} → A → Vec A n → Vec A (suc n)
_∷_ {n = 0}     x _  = x
_∷_ {n = suc _} x xs = x , xs

elim
  : ∀{ℓᵃ ℓ} {A : Type ℓᵃ} (P : ∀[ n ꞉ ℕ ] (Vec A n → Type ℓ))
  → P (lift tt)
  → ∀[ n ꞉ ℕ ] ∀[ x ꞉ A ] ∀[ xs ꞉ Vec A n ] (P xs → P (x ∷ xs))
  → {n : ℕ} (xs : Vec A n) → P xs
elim _ p[] _  {0} _ = p[]
elim _ p[] p∷ {1} x = p∷ p[]
elim P p[] p∷ {suc (suc _)} (x , xs) = p∷ (elim P p[] p∷ xs)

impl : VecI Vec
impl .VecI.[] = _
impl .VecI._∷_ = _∷_
impl .VecI.elim = elim

rec = VecI.rec impl

head : ∀{n} → Vec A (suc n) → A
head {n = 0}     x       = x
head {n = suc _} (x , _) = x

tail : ∀{n} → Vec A (suc n) → Vec A n
tail {n = 0}     _        = _
tail {n = suc _} (_ , xs) = xs

replicate : Π[ n ꞉ ℕ ] (A → Vec A n)
replicate 0       _ = _
replicate (suc n) x = x ∷ replicate n x


-- vector displayed over another vector

Vecᵈ : (B : A → Type ℓ′) {n : ℕ} (xs : Vec A n) → Type ℓ′
Vecᵈ B {0} _ = ⊤
Vecᵈ B {1} x = B x
Vecᵈ B {suc (suc n)} (x , xs) = B x × Vecᵈ B xs
