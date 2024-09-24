{-# OPTIONS --safe #-}
module Data.Tri.Base where

open import Foundations.Prelude
open import Data.Empty.Base
open import Data.Bool.Base
open import Data.Sum.Base

data Tri {o ℓ} {T : 𝒰 ℓ} (_<_ : T → T → 𝒰 o) (x y : T) : 𝒰 (ℓ ⊔ o) where
  lt : (x<y :   x < y) (x≠y : x ≠ y) (y≮x : ¬ y < x) → Tri _<_ x y
  eq : (x≮y : ¬ x < y) (x=y : x ＝ y) (y≮x : ¬ y < x) → Tri _<_ x y
  gt : (x≮y : ¬ x < y) (x≠y : x ≠ y) (y<x :   y < x) → Tri _<_ x y

private variable
  o ℓ ℓ′ : Level

Tri-elim : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o} {x y : T} {C : Tri _<_ x y → 𝒰 ℓ′}
         → ((x<y :   x < y) (x≠y : x ≠ y) (y≮x : ¬ y < x) → C (lt x<y x≠y y≮x))
         → ((x≮y : ¬ x < y) (x=y : x ＝ y) (y≮x : ¬ y < x) → C (eq x≮y x=y y≮x))
         → ((x≮y : ¬ x < y) (x≠y : x ≠ y) (y<x :   y < x) → C (gt x≮y x≠y y<x))
         → (t : Tri _<_ x y) → C t
Tri-elim tlt _   _   (lt x<y x≠y y≮x) = tlt x<y x≠y y≮x
Tri-elim _   teq _   (eq x≮y x=y y≮x) = teq x≮y x=y y≮x
Tri-elim _   _   tgt (gt x≮y x≠y y<x) = tgt x≮y x≠y y<x

{-
asym-connex→Tri : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o}
                   → (∀ {x y} → x < y → ¬ (y < x))
                   → (∀ {x y} → (x ＝ y) ⊎ (x < y) ⊎ (y < x))
                   → ∀ {x y} → Tri _<_ x y
asym-connex→Tri {_<_} as co {x} {y} with co {x} {y}
... | inl x=y       =
        eq (λ x<y → as x<y (subst (_< x) x=y $ subst (x <_) (x=y ⁻¹) x<y))
           x=y
           λ y<x → as ((subst (x <_) x=y $ subst (_< x) (x=y ⁻¹) y<x)) y<x
... | inr (inl x<y) =
        lt x<y
           (λ x=y → as x<y (subst (_< x) x=y $ subst (x <_) (x=y ⁻¹) x<y))
           (as x<y)
... | inr (inr y<x) =
        gt (as y<x)
           (λ x=y → as ((subst (x <_) x=y $ subst (_< x) (x=y ⁻¹) y<x)) y<x)
           y<x
-}

{- boolean projections -}

⌊_⌋< : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o} {x y : T}
     → Tri _<_ x y → Bool
⌊ lt _ _ _ ⌋< = true
⌊ eq _ _ _ ⌋< = false
⌊ gt _ _ _ ⌋< = false

⌊_⌋≤ : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o} {x y : T}
    → Tri _<_ x y → Bool
⌊ lt _ _ _ ⌋≤ = true
⌊ eq _ _ _ ⌋≤ = true
⌊ gt _ _ _ ⌋≤ = false
