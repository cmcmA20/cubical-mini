{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Base where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Nat.Base
  using (ℕ; zero; suc; _+_)
  public
open import Data.Vec.Interface

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  @0 m n : ℕ

infixr 5 _∷_
data Vec (A : Type ℓ) : @0 ℕ → Type ℓ where
  []  : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

elim
  : (P : ∀ᴱ[ n ꞉ ℕ ] (Vec A n → Type ℓ′))
  → P []
  → (∀ᴱ[ n ꞉ ℕ ] ∀[ x ꞉ A ] ∀[ xs ꞉ Vec A n ] (P xs → P (x ∷ xs)))
  → ∀ᴱ[ n ꞉ ℕ ] Π[ xs ꞉ Vec A n ] P xs
elim P p[] p∷ []       = p[]
elim P p[] p∷ (x ∷ xs) = p∷ (elim P p[] p∷ xs)

impl : VecIᴱ Vec
impl .VecIᴱ.[] = []
impl .VecIᴱ._∷_ = _∷_
impl .VecIᴱ.elim = elim

rec = VecIᴱ.rec impl

replicate : (n : ℕ) → A → Vec A n
replicate 0       x = []
replicate (suc n) x = x ∷ replicate n x

_++_ : Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

head : Vec A (suc n) → A
head (x ∷ _) = x

tail : Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

zip-with : (A → B → C) → Vec A n → Vec B n → Vec C n
zip-with f []       []       = []
zip-with f (x ∷ xs) (y ∷ ys) = f x y ∷ zip-with f xs ys

module _ where
  open import Data.Vec.Base
    using ()
    renaming (Vec to Vecᵈ)

  default≃inductive : ∀ {n} → Vecᵈ A n ≃ Vec A n
  default≃inductive {A} = iso→≃ $ to , iso from ri li where
    to : ∀{n} → Vecᵈ A n → Vec A n
    to {n = 0}     _        = []
    to {n = suc _} (x , xs) = x ∷ to xs

    from : ∀{n} → Vec A n → Vecᵈ A n
    from {n = 0}     _        = _
    from {n = suc _} (x ∷ xs) = x , from xs

    ri : ∀ {n} xs → to {n = n} (from xs) ＝ xs
    ri {n = 0}     []      = refl
    ri {n = suc _} (x ∷ _) = ap (x ∷_) (ri _)

    li : ∀ {n} xs → from {n = n} (to xs) ＝ xs
    li {n = 0}     _       = refl
    li {n = suc _} (x , _) = ap (x ,_) (li _)

  module default≃inductive {ℓ} {A} {n} = Equiv (default≃inductive {ℓ} {A} {n})
