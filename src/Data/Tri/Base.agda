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

Tri-rec : {T : 𝒰 ℓ} {_<_ : T → T → 𝒰 o} {x y : T} {A : 𝒰 ℓ′}
         → A → A → A → Tri _<_ x y → A
Tri-rec alt aeq agt t =
  Tri-elim (λ _ _ _ → alt) (λ _ _ _ → aeq) (λ _ _ _ → agt) t

{- TODO specialize for StrictPoset -}

caseᵗ-lt_&_&_return_of_ :
    {T : 𝒰 ℓ}
    {_<_ : T → T → 𝒰 o} ⦃ <-pr : ∀ {x y} → H-Level 1 (x < y) ⦄
    {x y : T} 
  → (x<y : x < y) (x≠y : x ≠ y) (y≮x : ¬ y < x)
  → (C : Tri _<_ x y → 𝒰 ℓ′)
  → C (lt x<y x≠y y≮x)
  → {t : Tri _<_ x y} → C t
caseᵗ-lt_&_&_return_of_ x<y x≠y y≮x C clt {t} =
  Tri-elim {C = C}
    (λ x<y′ x≠y′ y≮x′ →
      subst (λ q → C (lt q x≠y′ y≮x′)) prop! $
      subst (λ q → C (lt x<y q y≮x′)) prop! $
      subst (C ∘ lt x<y x≠y) prop! clt)
    (λ _ x=y _ → absurd (x≠y x=y))
    (λ x≮y _ _ → absurd (x≮y x<y))
    t

caseᵗ-eq_&_&_return_of_ :
    {T : 𝒰 ℓ} ⦃ T-st : H-Level 2 T ⦄
    {_<_ : T → T → 𝒰 o} ⦃ <-pr : ∀ {x y} → H-Level 1 (x < y) ⦄
    {x y : T} 
  → (x≮y : ¬ x < y) (x=y : x ＝ y) (y≮x : ¬ y < x)
  → (C : Tri _<_ x y → 𝒰 ℓ′)
  → C (eq x≮y x=y y≮x)
  → {t : Tri _<_ x y} → C t
caseᵗ-eq_&_&_return_of_ x≮y x=y y≮x C ceq {t} =
  Tri-elim {C = C}
    (λ _ x≠y _ → absurd (x≠y x=y))
    (λ x≮y′ x=y′ y≮x′ →
      subst (λ q → C (eq q x=y′ y≮x′)) prop! $
      subst (λ q → C (eq x≮y q y≮x′)) prop! $
      subst (C ∘ eq x≮y x=y) prop! ceq)
    (λ _ x≠y _ → absurd (x≠y x=y))
    t

caseᵗ-gt_&_&_return_of_ :
    {T : 𝒰 ℓ}
    {_<_ : T → T → 𝒰 o} ⦃ <-pr : ∀ {x y} → H-Level 1 (x < y) ⦄
    {x y : T} 
  → (x≮y : ¬ x < y) (x≠y : x ≠ y) (y<x : y < x)
  → (C : Tri _<_ x y → 𝒰 ℓ′)
  → C (gt x≮y x≠y y<x)
  → {t : Tri _<_ x y} → C t
caseᵗ-gt_&_&_return_of_ x≮y x≠y y<x C cgt {t} =
  Tri-elim {C = C}
    (λ _ _ y≮x → absurd (y≮x y<x))
    (λ _ x=y _ → absurd (x≠y x=y))
    (λ x≮y′ x≠y′ y<x′ →
      subst (λ q → C (gt q x≠y′ y<x′)) prop! $
      subst (λ q → C (gt x≮y q y<x′)) prop! $
      subst (C ∘ gt x≮y x≠y) prop! cgt)
    t

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
