{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.Any where

open import Prelude
open import Correspondences.Base
open import Correspondences.Decidable
open import Data.List.Base
open import Data.Empty.Base
open import Data.Dec as Dec

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P Q R : Pred A ℓ′
  x : A
  @0 xs ys : List A

data Any {ℓ ℓ′} {A : Type ℓ} (P : Pred A ℓ′) : @0 List A → Type (ℓ ⊔ ℓ′) where
  here  : ∀ {x xs} → (px : P x) → Any P (x ∷ xs)
  there : ∀ {x xs} → (pxs : Any P xs) → Any P (x ∷ xs)

¬Any-[] : {P : Pred A ℓ′} → ¬ Any P []
¬Any-[] ()

¬Any-∷ : {P : Pred A ℓ′} {x : A} {xs : List A}
       → ¬ P x → ¬ Any P xs → ¬ Any P (x ∷ xs)
¬Any-∷ nx nxs (here px)   = nx px
¬Any-∷ nx nxs (there pxs) = nxs pxs

Has : A → @0 List A → Type (level-of-type A)
Has x = Any (_＝ x)
