{-# OPTIONS --safe #-}
module Data.Dec.Tri where

open import Foundations.Base

open import Data.Bool.Base using (Bool; false; true)

data Tri {ℓ ℓ′} {A : Type ℓ} (_<_ : A → A → Type ℓ′) (x y : A) : 𝒰 (ℓ ⊔ ℓ′) where
  LT : x <  y → Tri _<_ x y
  EQ : x ＝ y → Tri _<_ x y
  GT : y <  x → Tri _<_ x y

private variable
  ℓ : Level
  A : Type ℓ
  _<_ : A → A → Type ℓ
  x y : A

elim : {M : Tri _<_ x y → Type ℓ}
     → ((lt : x <  y) → M (LT lt))
     → ((eq : x ＝ y) → M (EQ eq))
     → ((gt : y <  x) → M (GT gt))
     → (t : Tri _<_ x y) → M t
elim p _ _ (LT x) = p x
elim _ q _ (EQ x) = q x
elim _ _ r (GT x) = r x

rec : A → A → A → Tri _<_ x y → A
rec p q r = elim (λ _ → p) (λ _ → q) (λ _ → r)

is-lt? is-eq? is-gt? : Tri _<_ x y → Bool
is-lt? = rec true  false false
is-eq? = rec false true  false
is-gt? = rec false false true
