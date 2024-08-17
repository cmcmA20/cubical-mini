{-# OPTIONS --safe --no-exact-split #-}
module Data.Sum.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Functions.Embedding

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base
open import Data.Reflects.Base as Reflects
open import Data.Sum.Base
open import Data.Unit.Base

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  x : A
  y : B
  b : Bool

instance
  Extensional-⊎
    : ∀ {ℓr ℓs} {A : Type ℓᵃ} {B : Type ℓᵇ}
    → ⦃ sa : Extensional A ℓr ⦄
    → ⦃ sb : Extensional B ℓs ⦄
    → Extensional (A ⊎ B) (ℓr ⊔ ℓs)
  Extensional-⊎ {ℓs} ⦃ sa ⦄ .Pathᵉ (inl x) (inl x′) = Lift ℓs (Pathᵉ sa x x′)
  Extensional-⊎ {ℓr} ⦃ sb ⦄ .Pathᵉ (inr y) (inr y′) = Lift ℓr (Pathᵉ sb y y′)
  Extensional-⊎ .Pathᵉ _ _ = ⊥
  Extensional-⊎ ⦃ sa ⦄ .reflᵉ (inl x) = lift (reflᵉ sa x)
  Extensional-⊎ ⦃ sb ⦄ .reflᵉ (inr y) = lift (reflᵉ sb y)
  Extensional-⊎ ⦃ sa ⦄ .idsᵉ .to-path {inl x} {inl x′} (lift p) = ap inl $ sa .idsᵉ .to-path p
  Extensional-⊎ ⦃ sb ⦄ .idsᵉ .to-path {inr y} {inr y′} (lift p) = ap inr $ sb .idsᵉ .to-path p
  Extensional-⊎ ⦃ sa ⦄ .idsᵉ .to-path-over {inl x} {inl x′} (lift p) = apᴾ (λ _ → lift) $ sa .idsᵉ .to-path-over p
  Extensional-⊎ ⦃ sb ⦄ .idsᵉ .to-path-over {inr y} {inr y′} (lift p) = apᴾ (λ _ → lift) $ sb .idsᵉ .to-path-over p

opaque
  code-is-of-hlevel : {s₁ s₂ : A ⊎ B} {n : HLevel}
                    → is-of-hlevel (2 + n) A
                    → is-of-hlevel (2 + n) B
                    → is-of-hlevel (1 + n) (Extensional-⊎ .Pathᵉ s₁ s₂)
  code-is-of-hlevel {s₁ = inl x₁} {inl x₂} {n} ahl bhl = Lift-is-of-hlevel (suc n) (ahl x₁ x₂)
  code-is-of-hlevel {s₁ = inl x}  {inr y}  {n} ahl bhl = hlevel (suc n)
  code-is-of-hlevel {s₁ = inr x}  {inl y}  {n} ahl bhl = hlevel (suc n)
  code-is-of-hlevel {s₁ = inr y₁} {inr y₂} {n} ahl bhl = Lift-is-of-hlevel (suc n) (bhl y₁ y₂)

  ⊎-is-of-hlevel : (n : HLevel)
                 → is-of-hlevel (2 + n) A
                 → is-of-hlevel (2 + n) B
                 → is-of-hlevel (2 + n) (A ⊎ B)
  ⊎-is-of-hlevel n ahl bhl s₁ s₂ =
    ≃→is-of-hlevel (1 + n) (identity-system-gives-path (Extensional-⊎ .idsᵉ) ⁻¹)
      (code-is-of-hlevel {s₁ = s₁} {s₂ = s₂} ahl bhl)

  disjoint-⊎-is-prop
    : is-prop A → is-prop B → ¬ A × B
    → is-prop (A ⊎ B)
  disjoint-⊎-is-prop Ap Bp ¬ab (inl x₁) (inl x₂) = ap inl (Ap x₁ x₂)
  disjoint-⊎-is-prop Ap Bp ¬ab (inl x)  (inr y)  = false! (¬ab (x , y))
  disjoint-⊎-is-prop Ap Bp ¬ab (inr x)  (inl y)  = false! (¬ab (y , x))
  disjoint-⊎-is-prop Ap Bp ¬ab (inr y₁) (inr y₂) = ap inr (Bp y₁ y₂)

  prop-⊎-is-set
    : is-prop A → is-prop B
    → is-set (A ⊎ B)
  prop-⊎-is-set {A} {B} A-prop B-prop = identity-system→is-of-hlevel 1 (Extensional-⊎ .idsᵉ) go where
    go : (x y : A ⊎ B) → is-prop (Extensional-⊎ .Pathᵉ x y)
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
inl-inj {A} {x} = ap [ id , (λ _ → x) ]ᵤ

inr-inj : {x y : B} → inr {A = A} x ＝ inr y → x ＝ y
inr-inj {B} {x} = ap [ (λ _ → x) , id ]ᵤ

inl-cancellable : {A : Type ℓᵃ} {B : Type ℓᵇ} → Cancellable {A = A} {B = A ⊎ B} inl
inl-cancellable = identity-system-gives-path (Extensional-⊎ .idsᵉ) ⁻¹ ∙ lift≃id

inl-is-embedding : {A : Type ℓᵃ} → is-embedding {A = A} {B = A ⊎ B} inl
inl-is-embedding = cancellable→is-embedding inl-cancellable

inr-cancellable : {A : Type ℓᵃ} {B : Type ℓᵇ} → Cancellable {A = B} {B = A ⊎ B} inr
inr-cancellable = identity-system-gives-path (Extensional-⊎ .idsᵉ) ⁻¹ ∙ lift≃id

inr-is-embedding : {B : Type ℓᵇ} → is-embedding {A = B} {B = A ⊎ B} inr
inr-is-embedding = cancellable→is-embedding inr-cancellable

instance
  Reflects-inl≠inr : Reflects (inl x ＝ inr y) false
  Reflects-inl≠inr = ofⁿ λ p → ¬-so-false (subst So (ap is-inl? p) oh)

  Reflects-inr≠inl : Reflects (inr y ＝ inl x) false
  Reflects-inr≠inl = reflects-sym auto

  Reflects-inl=inl : ⦃ Reflects (Path A x y) b ⦄ → Reflects (Path (A ⊎ B) (inl x) (inl y)) b
  Reflects-inl=inl = Reflects.dmap (ap inl) (contra inl-inj) auto

  Reflects-inr=inr : ⦃ Reflects (Path B x y) b ⦄ → Reflects (Path (A ⊎ B) (inr x) (inr y)) b
  Reflects-inr=inr = Reflects.dmap (ap inr) (contra inr-inj) auto

  ⊎-is-discrete : ⦃ _ : is-discrete A ⦄ ⦃ _ : is-discrete B ⦄ → is-discrete (A ⊎ B)
  ⊎-is-discrete {x = inl x} {inl x′} = x =? x′ because auto
  ⊎-is-discrete {x = inl x} {inr y}  = false because auto
  ⊎-is-discrete {x = inr y} {inl x}  = false because auto
  ⊎-is-discrete {x = inr y} {inr y′} = y =? y′ because auto


-- Automation
instance opaque
  H-Level-⊎
    : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → ⦃ A-hl : H-Level n A ⦄ → ⦃ B-hl : H-Level n B ⦄
    → H-Level n (A ⊎ B)
  H-Level-⊎ {n} ⦃ s≤ʰs (s≤ʰs _) ⦄ .H-Level.has-of-hlevel = ⊎-is-of-hlevel _ (hlevel n) (hlevel n)
  {-# OVERLAPS H-Level-⊎ #-}

opaque
  disjoint-⊎-is-prop!
    : ⦃ A-pr : H-Level 1 A ⦄ → ⦃ B-pr : H-Level 1 B ⦄
    → ¬ A × B → is-prop (A ⊎ B)
  disjoint-⊎-is-prop! = disjoint-⊎-is-prop (hlevel 1) (hlevel 1)
