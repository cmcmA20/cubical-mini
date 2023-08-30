{-# OPTIONS --safe #-}
module Data.Product.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Correspondences.Finite.Bishop

open import Data.Unit.Instances.Finite
open import Data.Vec.Base

open import Data.Product.Base public

private variable
  ℓ ℓ′ : Level
  n : ℕ
  A : Type ℓ
  B : Type ℓ′

HProduct≃Vec : HProduct n A ≃ Vec A n
HProduct≃Vec {A} = iso→equiv (f , iso g a→b→a b→a→b) where
  f : HProduct n A → Vec A n
  f {n = 0} _ = []
  f {n = 1} x = x ∷ []
  f {n = suc (suc n)} (x , xs) = x ∷ f xs

  g : Vec A n → HProduct n A
  g {n = 0} _       = lift tt
  g {n = 1} (x ∷ _) = x
  g {n = suc (suc n)} (x ∷ xs) = x , g xs

  a→b→a : (xs : Vec A n) → f (g xs) ＝ xs
  a→b→a {n = 0} []       = refl
  a→b→a {n = 1} (x ∷ []) = refl
  a→b→a {n = suc (suc n)} (x ∷ xs) = ap (x ∷_) (a→b→a _)

  b→a→b : (xs : HProduct n A) → g (f xs) ＝ xs
  b→a→b {n = 0} _ = refl
  b→a→b {n = 1} _ = refl
  b→a→b {n = suc (suc n)} (x , xs) = ap (x ,_) (b→a→b xs)


-- FIXME decomp
instance
  hproduct-is-fin-set : {ℓ : Level} {A : Type ℓ} {n : ℕ}
                  → ⦃ is-fin-set A ⦄ → is-fin-set (HProduct n A)
  hproduct-is-fin-set {A} {0} = lift-is-fin-set ⊤-is-fin-set
  hproduct-is-fin-set {A} {1} ⦃ (A-fin) ⦄ = A-fin
  hproduct-is-fin-set {A} {suc (suc n)} ⦃ (A-fin) ⦄ =
    ×-is-fin-set A-fin (hproduct-is-fin-set {A = A} {n = suc n} ⦃ A-fin ⦄)
