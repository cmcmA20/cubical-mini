{-# OPTIONS --safe #-}
module Data.Nat.Path where

open import Foundations.Base

open import Data.Empty

open import Structures.IdentitySystem.Base

open import Data.Nat.Base public

-- only to illustrate the method
module ℕ-path-code where

  Code : ℕ → ℕ → Type
  Code zero    zero    = ⊤
  Code zero    (suc n) = ⊥
  Code (suc m) zero    = ⊥
  Code (suc m) (suc n) = Code m n

  code-refl : (m : ℕ) → Code m m
  code-refl zero    = tt
  code-refl (suc m) = code-refl m

  decode : ∀ m n → Code m n → m ＝ n
  decode zero    zero    _ = refl
  decode (suc m) (suc n) c = ap suc (decode m n c)

  ℕ-identity-system : is-identity-system Code code-refl
  ℕ-identity-system .to-path = decode _ _
  ℕ-identity-system .to-path-over {a} {b} = go a b
    where
    go : ∀ m n → (c : Code m n)
       → ＜ code-refl m ／ (λ i → Code m (decode m n c i)) ＼ c ＞
    go zero    zero    _ = refl
    go (suc m) (suc n) c = go m n c
