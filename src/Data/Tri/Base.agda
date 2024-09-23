{-# OPTIONS --safe #-}
module Data.Tri.Base where

open import Foundations.Prelude
open import Data.Empty.Base
open import Data.Bool.Base

private variable
  o ℓ : Level

data Tri {ℓo} {ℓ} {T : Type ℓ} (_<_ : T → T → Type ℓo) (x y : T) : Type (ℓ ⊔ ℓo) where
  lt : (x<y :   x < y) (x≠y : ¬ x ＝ y) (y≮x : ¬ y < x) → Tri _<_ x y
  eq : (x≮y : ¬ x < y) (x=y :   x ＝ y) (y≮x : ¬ y < x) → Tri _<_ x y
  gt : (x≮y : ¬ x < y) (x≠y : ¬ x ＝ y) (y<x :   y < x) → Tri _<_ x y

Tri-elim : {ℓo ℓ ℓ′ : Level} {T : Type ℓ} {_<_ : T → T → Type ℓo} {x y : T}
           {C : Tri _<_ x y → Type ℓ′}
         → ((x<y :   x < y) (x≠y : ¬ x ＝ y) (y≮x : ¬ y < x) → C (lt x<y x≠y y≮x))
         → ((x≮y : ¬ x < y) (x=y :   x ＝ y) (y≮x : ¬ y < x) → C (eq x≮y x=y y≮x))
         → ((x≮y : ¬ x < y) (x≠y : ¬ x ＝ y) (y<x :   y < x) → C (gt x≮y x≠y y<x))
         → (t : Tri _<_ x y) → C t
Tri-elim tlt teq tgt (lt x<y x≠y y≮x) = tlt x<y x≠y y≮x
Tri-elim tlt teq tgt (eq x≮y x=y y≮x) = teq x≮y x=y y≮x
Tri-elim tlt teq tgt (gt x≮y x≠y y<x) = tgt x≮y x≠y y<x

⌊_⌋< : {ℓo ℓ : Level} {T : Type ℓ} {_<_ : T → T → Type ℓo} {x y : T}
     → Tri _<_ x y → Bool
⌊ lt _ _ _ ⌋< = true
⌊ eq _ _ _ ⌋< = false
⌊ gt _ _ _ ⌋< = false

⌊_⌋≤ : {ℓo ℓ : Level} {T : Type ℓ} {_<_ : T → T → Type ℓo} {x y : T}
     → Tri _<_ x y → Bool
⌊ lt _ _ _ ⌋≤ = true
⌊ eq _ _ _ ⌋≤ = true
⌊ gt _ _ _ ⌋≤ = false
