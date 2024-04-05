{-# OPTIONS --safe #-}
module Meta.Ord where

open import Foundations.Base

open import Correspondences.Discrete

open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥

open import Truncation.Propositional.Base

-- TODO move this out
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


record Ord {ℓ} (T : Type ℓ) : Typeω where
  no-eta-equality
  field
    ℓo      : Level
    _<_     : T → T → Type ℓo
    <-thin  : ∀ {x y} → is-prop (x < y)
    <-trans : ∀ {x y z} → x < y → y < z → x < z
    _≤?_    : (x y : T) → Tri _<_ x y

open Ord ⦃ ... ⦄
  using (_<_; _≤?_)
  public

open Ord using (<-thin; <-trans)

private variable
  ℓ : Level
  T : Type ℓ

instance
  ord→is-discrete : ⦃ ord : Ord T ⦄ → is-discrete T
  ord→is-discrete {x} {y} with x ≤? y
  ... | lt _ x≠y _ = no  x≠y
  ... | eq _ x=y _ = yes x=y
  ... | gt _ x≠y _ = no  x≠y
  {-# OVERLAPPABLE ord→is-discrete #-}
