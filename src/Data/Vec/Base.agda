{-# OPTIONS --safe #-}
module Data.Vec.Base where

open import Foundations.Base

open import Data.Nat.Base
  using (ℕ; zero; suc)
  public
open import Data.Vec.Interface

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

Vec : Type ℓ → (n : ℕ) → Type ℓ
Vec _ 0       = Lift _ ⊤
Vec A (suc n) = A × Vec A n

infixr 5 _∷_
_∷_ : ∀ᴱ[ n ꞉ ℕ ] (A → Vec A n → Vec A (suc n))
x ∷ xs = x , xs

elim
  : (P : ∀[ n ꞉ ℕ ] (Vec A n → Type ℓ))
  → P (lift tt)
  → ∀[ n ꞉ ℕ ] ∀[ x ꞉ A ] ∀[ xs ꞉ Vec A n ] (P xs → P (x ∷ xs))
  → ∀[ n ꞉ ℕ ] Π[ xs ꞉ Vec A n ] P xs
elim P p[] p∷ {0} _ = p[]
elim P p[] p∷ {suc _} (x , xs) = p∷ (elim P p[] p∷ xs)

impl : VecI Vec
impl .VecI.[] = _
impl .VecI._∷_ = _∷_
impl .VecI.elim = elim

rec = VecI.rec impl

head : ∀ᴱ[ n ꞉ ℕ ] (Vec A (suc n) → A)
head (x , _) = x

tail : ∀ᴱ[ n ꞉ ℕ ] (Vec A (suc n) → Vec A n)
tail (_ , xs) = xs

replicate : Π[ n ꞉ ℕ ] (A → Vec A n)
replicate 0       _ = _
replicate (suc n) x = x ∷ replicate n x
