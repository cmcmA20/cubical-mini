{-# OPTIONS --safe #-}
module Data.Fin.Properties where

open import Foundations.Base
open import Foundations.Equiv.Base

open import Data.Empty.Base
open import Data.Nat.Path
open import Data.Nat.Order
import      Data.Sum.Base as ⊎
open ⊎

open import Data.Fin.Base

private variable
  ℓ : Level
  m n : ℕ

cast : m ＝ n → Fin m → Fin n
cast {suc m} {(zero)} p _ = absurd (suc≠zero p)
cast {suc m} {suc n}  _ fzero    = fzero
cast {suc m} {suc n}  p (fsuc k) = fsuc (cast (suc-inj p) k)

cast-is-equiv : (p : m ＝ n) → is-equiv (cast p)
cast-is-equiv = J (λ _ p → is-equiv (cast p)) cast-refl-is-equiv
  where
    id＝cast-refl : id ＝ cast (λ _ → n)
    id＝cast-refl {(zero)} _ ()
    id＝cast-refl {suc n} _ fzero = fzero
    id＝cast-refl {suc n} i (fsuc k) = fsuc (id＝cast-refl i k)

    cast-refl-is-equiv : is-equiv (cast (λ _ → n))
    cast-refl-is-equiv = subst is-equiv id＝cast-refl id-is-equiv

cast-equiv : m ＝ n → Fin m ≃ Fin n
cast-equiv p = cast p , cast-is-equiv p

strengthen : Fin (suc n) → Fin (suc n) ⊎ Fin n
strengthen {(zero)} fzero = inl fzero
strengthen {suc n}  fzero = inr fzero
strengthen {suc n}  (fsuc k) = ⊎.map fsuc fsuc (strengthen k)

inject : m ≤ n → Fin m → Fin n
inject {_} {suc n} le       fzero    = fzero
inject {_} {suc n} (s≤s le) (fsuc k) = fsuc (inject le k)
