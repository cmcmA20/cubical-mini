{-# OPTIONS --safe #-}
module Data.Tri.Base where

open import Foundations.Prelude
open import Data.Empty.Base renaming (elim to elimᵉ ; rec to recᵉ)
open import Data.Bool.Base renaming (elim to elimᵇ ; rec to recᵇ)
open import Data.Sum.Base
open import Data.Dec.Base renaming (elim to elimᵈ ; rec to recᵈ)

data Tri {o ℓ} {T : 𝒰 ℓ} (_<_ : T → T → 𝒰 o) (x y : T) : 𝒰 (ℓ ⊔ o) where
  lt : (x<y :   x < y) (x≠y : x ≠ y) (y≮x : ¬ y < x) → Tri _<_ x y
  eq : (x≮y : ¬ x < y) (x=y : x ＝ y) (y≮x : ¬ y < x) → Tri _<_ x y
  gt : (x≮y : ¬ x < y) (x≠y : x ≠ y) (y<x :   y < x) → Tri _<_ x y

private variable
  o ℓ ℓ′ : Level

elim : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o} {x y : T} {C : Tri _<_ x y → 𝒰 ℓ′}
     → ((x<y :   x < y) (x≠y : x ≠ y) (y≮x : ¬ y < x) → C (lt x<y x≠y y≮x))
     → ((x≮y : ¬ x < y) (x=y : x ＝ y) (y≮x : ¬ y < x) → C (eq x≮y x=y y≮x))
     → ((x≮y : ¬ x < y) (x≠y : x ≠ y) (y<x :   y < x) → C (gt x≮y x≠y y<x))
     → (t : Tri _<_ x y) → C t
elim tlt _   _   (lt x<y x≠y y≮x) = tlt x<y x≠y y≮x
elim _   teq _   (eq x≮y x=y y≮x) = teq x≮y x=y y≮x
elim _   _   tgt (gt x≮y x≠y y<x) = tgt x≮y x≠y y<x

rec : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o} {x y : T} {A : 𝒰 ℓ′}
    → A → A → A → Tri _<_ x y → A
rec alt aeq agt t =
  elim (λ _ _ _ → alt) (λ _ _ _ → aeq) (λ _ _ _ → agt) t

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

{- decidable projections -}

⌊_⌋≟ : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o} {x y : T}
    → Tri _<_ x y → Dec (x ＝ y)
⌊_⌋≟ = elim (λ _ x≠y _ → no x≠y) (λ _ x=y _ → yes x=y) (λ _ x≠y _ → no x≠y)

-- TODO running out of symbol ideas
⌊_⌋<¿ : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o} {x y : T}
      → Tri _<_ x y → Dec (x < y)
⌊_⌋<¿ = elim (λ x<y _ _ → yes x<y) (λ x≮y _ _ → no x≮y) (λ x≮y _ _ → no x≮y)

{- boolean projections -}

⌊_⌋< : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o} {x y : T}
     → Tri _<_ x y → Bool
⌊_⌋< = rec true false false

⌊_⌋≤ : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o} {x y : T}
    → Tri _<_ x y → Bool
⌊_⌋≤ = rec true true false
