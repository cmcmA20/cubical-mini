{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.At where

open import Prelude

open import Data.List.Base
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.Nat.Base
open import Data.Nat.Order.Base
open import Data.Reflects as Reflects

private variable
  ℓᵃ ℓ : Level
  A : 𝒰 ℓᵃ
  P Q R : Pred A ℓ
  x : A
  @0 xs ys : List A

data At {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (P : Pred A ℓ) : @0 List A → @0 ℕ → 𝒰 (ℓᵃ ⊔ ℓ) where
  ahere  : ∀ {x} {@0 xs : List A} → (px : P x) → At P (x ∷ xs) zero
  athere : ∀ {n x} {@0 xs : List A} → (pxs : At P xs n) → At P (x ∷ xs) (suc n)

all→at : {xs : List A}
       → All P xs → ∀ n → n < length xs → At P xs n
all→at {xs = []}      a       n      nlt = false! nlt
all→at {xs = x ∷ xs} (px ∷ _) zero   nlt = ahere px
all→at {xs = x ∷ xs} (_ ∷ a) (suc n) nlt = athere (all→at a n (<-peel nlt))

any→at : {@0 xs : List A}
       → (a : Any P xs) → At P xs (any→ℕ a)
any→at (here px) = ahere px
any→at (there a) = athere (any→at a)

-- the weak version, allowing the element to not be included

data AtWeak {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (P : Pred A ℓ) : @0 List A → @0 ℕ → 𝒰 (ℓᵃ ⊔ ℓ) where
  awnil  : ∀ {n} → AtWeak P [] n
  awhere  : ∀ {x xs} → (px : P x) → AtWeak P (x ∷ xs) zero
  awthere : ∀ {n x xs} → (pxs : AtWeak P xs n) → AtWeak P (x ∷ xs) (suc n)

at→atweak : ∀ {xs n} → At P xs n → AtWeak P xs n
at→atweak {xs = x ∷ xs} (ahere px) = awhere px
at→atweak {xs = x ∷ xs} (athere a) = awthere (at→atweak a)

all→atweak : ∀ {xs} → All P xs → ∀ n → AtWeak P xs n
all→atweak {xs = []}     []        n      = awnil
all→atweak {xs = x ∷ xs} (px ∷ _)  zero   = awhere px
all→atweak {xs = x ∷ xs} (_ ∷ a)  (suc n) = awthere (all→atweak a n)
