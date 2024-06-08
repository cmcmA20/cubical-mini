{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Path where

open import Meta.Prelude

open import Data.Empty.Base as ⊥
open import Data.Nat.Path
open import Data.Vec.Inductive.Base

private variable
  ℓ : Level
  A : 𝒰 ℓ
  m n : ℕ

vec-cast : m ＝ n → Vec A m → Vec A n
vec-cast {0}     {0}     _ xs       = xs
vec-cast {suc m} {suc n} p (x ∷ xs) = x ∷ vec-cast (suc-inj p) xs
vec-cast {0}     {suc n} p          = ⊥.rec $ zero≠suc $ p
vec-cast {suc m} {0}     p          = ⊥.rec $ suc≠zero $ p

vec-cast-coh : (m n : ℕ) (p : m ＝ n) (xs : Vec A m) → vec-cast p xs ＝ substₚ (λ n → Vec A n) p xs
vec-cast-coh 0 = Jₚ> λ where
  [] → transport-refl _ ⁻¹
vec-cast-coh (suc m) = Jₚ> λ where
  (x ∷ xs) → ap (x ∷_) (vec-cast-coh m m refl xs ∙ transport-refl _) ∙ transport-refl (x ∷ xs) ⁻¹

instance
  vec-transport-system : is-transport-system {B = λ n → Vec A n} (erase path-identity-system)
  vec-transport-system .is-transport-system.subst     = vec-cast
  vec-transport-system .is-transport-system.subst-coh p b .erased = vec-cast-coh _ _ p b
