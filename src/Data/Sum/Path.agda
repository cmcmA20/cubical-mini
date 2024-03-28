{-# OPTIONS --safe #-}
module Data.Sum.Path where

open import Meta.Prelude

open import Meta.Extensionality
open import Meta.Search.HLevel

open import Structures.IdentitySystem.Base

open import Data.Empty.Base

open import Data.Sum.Base

private variable
  a b : Level
  A : Type a
  B : Type b
  x : A
  y : B

Code : A ⊎ B → A ⊎ B → Type (level-of-type A ⊔ level-of-type B)
Code {B} (inl x₁) (inl x₂) = Lift (level-of-type B) (x₁ ＝ x₂)
Code     (inl _)  (inr _)  = Lift _ ⊥
Code     (inr _)  (inl _)  = Lift _ ⊥
Code {A} (inr y₁) (inr y₂) = Lift (level-of-type A) (y₁ ＝ y₂)

code-refl : (s : A ⊎ B) → Code s s
code-refl (inl x) = lift refl
code-refl (inr y) = lift refl

identity-system : is-identity-system {A = A ⊎ B} Code code-refl
identity-system .to-path {inl x₁} {inl x₂} c = ap inl (lower c)
identity-system .to-path {inr y₁} {inr y₂} c = ap inr (lower c)
identity-system .to-path-over {inl x₁} {inl x₂} (lift p) i = lift λ j → p (i ∧ j)
identity-system .to-path-over {inr y₁} {inr y₂} (lift p) i = lift λ j → p (i ∧ j)

opaque
  unfolding is-of-hlevel
  code-is-of-hlevel : {s₁ s₂ : A ⊎ B} {n : HLevel}
                    → is-of-hlevel (2 + n) A
                    → is-of-hlevel (2 + n) B
                    → is-of-hlevel (1 + n) (Code s₁ s₂)
  code-is-of-hlevel {s₁ = inl x₁} {inl x₂} ahl bhl = Lift-is-of-hlevel _ (ahl x₁ x₂)
  code-is-of-hlevel {s₁ = inl x}  {inr y}  ahl bhl = hlevel!
  code-is-of-hlevel {s₁ = inr x}  {inl y}  ahl bhl = hlevel!
  code-is-of-hlevel {s₁ = inr y₁} {inr y₂} ahl bhl = Lift-is-of-hlevel _ (bhl y₁ y₂)

opaque
  unfolding is-of-hlevel
  ⊎-is-of-hlevel : (n : HLevel)
                 → is-of-hlevel (2 + n) A
                 → is-of-hlevel (2 + n) B
                 → is-of-hlevel (2 + n) (A ⊎ B)
  ⊎-is-of-hlevel n ahl bhl _ _ =
    ≃→is-of-hlevel (1 + n) (identity-system-gives-path identity-system ⁻¹) (code-is-of-hlevel ahl bhl)

  disjoint-⊎-is-prop
    : is-prop A → is-prop B → ¬ A × B
    → is-prop (A ⊎ B)
  disjoint-⊎-is-prop Ap Bp notab (inl x₁) (inl x₂) = ap inl (Ap x₁ x₂)
  disjoint-⊎-is-prop Ap Bp notab (inl x)  (inr y)  = absurd $ notab (x , y)
  disjoint-⊎-is-prop Ap Bp notab (inr x)  (inl y)  = absurd $ notab (y , x)
  disjoint-⊎-is-prop Ap Bp notab (inr y₁) (inr y₂) = ap inr (Bp y₁ y₂)

opaque
  unfolding is-of-hlevel
  prop-⊎-is-set
    : is-prop A → is-prop B
    → is-set (A ⊎ B)
  prop-⊎-is-set {A} {B} A-prop B-prop = identity-system→is-of-hlevel 1 identity-system go where
    go : (x y : A ⊎ B) → is-prop (Code x y)
    go (inl x)  (inr y)  = hlevel!
    go (inr y)  (inl x)  = hlevel!
    go (inl x₁) (inl x₂) = Lift-is-of-hlevel 1 $ is-prop→is-set A-prop _ _
    go (inr y₁) (inr y₂) = Lift-is-of-hlevel 1 $ is-prop→is-set B-prop _ _

contr-⊎-is-set
  : is-contr A → is-contr B
  → is-set (A ⊎ B)
contr-⊎-is-set A-contr B-contr = prop-⊎-is-set (is-contr→is-prop A-contr) (is-contr→is-prop B-contr)

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

instance
  decomp-hlevel-⊎
    : ∀ {a b} {A : Type a} {B : Type b}
    → goal-decomposition (quote is-of-hlevel) (A ⊎ B)
  decomp-hlevel-⊎ = decomp (quote ⊎-is-of-hlevel)
    [ `level-minus 2 , `search (quote is-of-hlevel) , `search (quote is-of-hlevel) ]

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
