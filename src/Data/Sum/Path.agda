{-# OPTIONS --safe #-}
module Data.Sum.Path where

open import Meta.Prelude

open import Meta.Extensionality

open import Data.Empty.Base
open import Data.Sum.Base

private variable
  a b : Level
  A : Type a
  B : Type b
  x : A
  y : B

instance
  Extensional-⊎
    : ∀ {ℓ ℓ′ ℓr ℓs} {A : Type ℓ} {B : Type ℓ′}
    → ⦃ sa : Extensional A ℓr ⦄
    → ⦃ sb : Extensional B ℓs ⦄
    → Extensional (A ⊎ B) (ℓr ⊔ ℓs)
  Extensional-⊎ {ℓs} ⦃ sa ⦄ .Pathᵉ (inl x) (inl x′) = Lift ℓs (Pathᵉ sa x x′)
  Extensional-⊎ {ℓr} ⦃ sb ⦄ .Pathᵉ (inr y) (inr y′) = Lift ℓr (Pathᵉ sb y y′)
  Extensional-⊎ .Pathᵉ _ _ = Lift _ ⊥
  Extensional-⊎ ⦃ sa ⦄ .reflᵉ (inl x) = lift (reflᵉ sa x)
  Extensional-⊎ ⦃ sb ⦄ .reflᵉ (inr y) = lift (reflᵉ sb y)
  Extensional-⊎ ⦃ sa ⦄ .idsᵉ .to-path {inl x} {inl x′} (lift p) = ap inl $ sa .idsᵉ .to-path p
  Extensional-⊎ ⦃ sb ⦄ .idsᵉ .to-path {inr y} {inr y′} (lift p) = ap inr $ sb .idsᵉ .to-path p
  Extensional-⊎ ⦃ sa ⦄ .idsᵉ .to-path-over {inl x} {inl x′} (lift p) = apᴾ (λ _ → lift) $ sa .idsᵉ .to-path-over p
  Extensional-⊎ ⦃ sb ⦄ .idsᵉ .to-path-over {inr y} {inr y′} (lift p) = apᴾ (λ _ → lift) $ sb .idsᵉ .to-path-over p

Code : (x y : A ⊎ B) → Type (level-of-type A ⊔ level-of-type B)
Code = Extensional-⊎ .Pathᵉ

code-refl : (x : A ⊎ B) → Extensional-⊎ .Pathᵉ x x
code-refl = Extensional-⊎ .reflᵉ

identity-system : is-identity-system {A = A ⊎ B} Code _
identity-system = Extensional-⊎ .idsᵉ

opaque
  code-is-of-hlevel : {s₁ s₂ : A ⊎ B} {n : HLevel}
                    → is-of-hlevel (2 + n) A
                    → is-of-hlevel (2 + n) B
                    → is-of-hlevel (1 + n) (Code s₁ s₂)
  code-is-of-hlevel {s₁ = inl x₁} {inl x₂} {n} ahl bhl = Lift-is-of-hlevel (suc n) (ahl x₁ x₂)
  code-is-of-hlevel {s₁ = inl x}  {inr y}  {n} ahl bhl = hlevel (suc n)
  code-is-of-hlevel {s₁ = inr x}  {inl y}  {n} ahl bhl = hlevel (suc n)
  code-is-of-hlevel {s₁ = inr y₁} {inr y₂} {n} ahl bhl = Lift-is-of-hlevel (suc n) (bhl y₁ y₂)

  ⊎-is-of-hlevel : (n : HLevel)
                 → is-of-hlevel (2 + n) A
                 → is-of-hlevel (2 + n) B
                 → is-of-hlevel (2 + n) (A ⊎ B)
  ⊎-is-of-hlevel n ahl bhl s₁ s₂ =
    ≃→is-of-hlevel (1 + n) (identity-system-gives-path identity-system ⁻¹)
      (code-is-of-hlevel {s₁ = s₁} {s₂ = s₂} ahl bhl)

  disjoint-⊎-is-prop
    : is-prop A → is-prop B → ¬ A × B
    → is-prop (A ⊎ B)
  disjoint-⊎-is-prop Ap Bp notab (inl x₁) (inl x₂) = ap inl (Ap x₁ x₂)
  disjoint-⊎-is-prop Ap Bp notab (inl x)  (inr y)  = absurd $ notab (x , y)
  disjoint-⊎-is-prop Ap Bp notab (inr x)  (inl y)  = absurd $ notab (y , x)
  disjoint-⊎-is-prop Ap Bp notab (inr y₁) (inr y₂) = ap inr (Bp y₁ y₂)

  prop-⊎-is-set
    : is-prop A → is-prop B
    → is-set (A ⊎ B)
  prop-⊎-is-set {A} {B} A-prop B-prop = identity-system→is-of-hlevel 1 identity-system go where
    go : (x y : A ⊎ B) → is-prop (Code x y)
    go (inl x)  (inr y)  = hlevel 1
    go (inr y)  (inl x)  = hlevel 1
    go (inl x₁) (inl x₂) = Lift-is-of-hlevel 1 $ is-prop→is-set A-prop _ _
    go (inr y₁) (inr y₂) = Lift-is-of-hlevel 1 $ is-prop→is-set B-prop _ _

  contr-⊎-is-set
    : is-contr A → is-contr B
    → is-set (A ⊎ B)
  contr-⊎-is-set A-contr B-contr = prop-⊎-is-set
    (is-contr→is-prop A-contr)
    (is-contr→is-prop B-contr)

inl-inj : {x y : A} → inl {B = B} x ＝ inl y → x ＝ y
inl-inj {A} {x} path = ap f path where
  f : A ⊎ B → A
  f (inl a) = a
  f (inr _) = x

inr-inj : {x y : B} → inr {A = A} x ＝ inr y → x ＝ y
inr-inj {B} {x} path = ap f path where
  f : A ⊎ B → B
  f (inl _) = x
  f (inr b) = b

⊎-disjoint : inl x ≠ inr y
⊎-disjoint p = subst ⊎-discrim p tt
  where
  ⊎-discrim : A ⊎ B → Type
  ⊎-discrim (inl _) = ⊤
  ⊎-discrim (inr _) = ⊥


-- Automation
instance opaque
  H-Level-⊎
    : ∀ {n} → ⦃ A-hl : H-Level (2 + n) A ⦄ → ⦃ B-hl : H-Level (2 + n) B ⦄
    → H-Level (2 + n) (A ⊎ B)
  H-Level-⊎ {n} .H-Level.has-of-hlevel = ⊎-is-of-hlevel n (hlevel (2 + n)) (hlevel (2 + n))

opaque
  disjoint-⊎-is-prop!
    : ⦃ A-pr : H-Level 1 A ⦄ → ⦃ B-pr : H-Level 1 B ⦄
    → ¬ A × B → is-prop (A ⊎ B)
  disjoint-⊎-is-prop! = disjoint-⊎-is-prop (hlevel 1) (hlevel 1)
