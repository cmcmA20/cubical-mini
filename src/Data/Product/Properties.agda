{-# OPTIONS --safe #-}
module Data.Product.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Correspondences.Nullary.Finite.Bishop

open import Data.Unit.Instances.Finite
open import Data.Vec.Base

open import Data.Product.Base public

private variable
  ℓ ℓ′ : Level
  n : ℕ
  A : Type ℓ
  B : Type ℓ′

Vecₓ≃Vec : Vecₓ A n ≃ Vec A n
Vecₓ≃Vec {A} = iso→equiv (f , iso g a→b→a b→a→b) where
  f : Vecₓ A n → Vec A n
  f {n = 0} _ = []
  f {n = 1} x = x ∷ []
  f {n = suc (suc n)} (x , xs) = x ∷ f xs

  g : Vec A n → Vecₓ A n
  g {n = 0} _       = lift tt
  g {n = 1} (x ∷ _) = x
  g {n = suc (suc n)} (x ∷ xs) = x , g xs

  a→b→a : (xs : Vec A n) → f (g xs) ＝ xs
  a→b→a {n = 0} []       = refl
  a→b→a {n = 1} (x ∷ []) = refl
  a→b→a {n = suc (suc n)} (x ∷ xs) = ap (x ∷_) (a→b→a _)

  b→a→b : (xs : Vecₓ A n) → g (f xs) ＝ xs
  b→a→b {n = 0} _ = refl
  b→a→b {n = 1} _ = refl
  b→a→b {n = suc (suc n)} (x , xs) = ap (x ,_) (b→a→b xs)


-- FIXME decomp
instance
  vecₓ-is-fin-set : {ℓ : Level} {A : Type ℓ} {n : ℕ}
                  → ⦃ is-fin-set A ⦄ → is-fin-set (Vecₓ A n)
  vecₓ-is-fin-set {A} {0} = lift-is-fin-set ⊤-is-fin-set
  vecₓ-is-fin-set {A} {1} ⦃ (A-fin) ⦄ = A-fin
  vecₓ-is-fin-set {A} {suc (suc n)} ⦃ (A-fin) ⦄ =
    ×-is-fin-set A-fin (vecₓ-is-fin-set {A = A} {n = suc n} ⦃ A-fin ⦄)
