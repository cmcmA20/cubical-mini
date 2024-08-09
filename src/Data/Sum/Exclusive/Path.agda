{-# OPTIONS --safe --no-exact-split #-}
module Data.Sum.Exclusive.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Functions.Embedding

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base as Reflects
open import Data.Sum.Exclusive.Base
open import Data.Unit.Base

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  a : A
  b : B
  x : Bool

instance
  Extensional-⊻
    : ∀ {ℓ ℓ′ ℓr ℓs} {A : Type ℓ} {B : Type ℓ′}
    → ⦃ sa : Extensional A ℓr ⦄
    → ⦃ sb : Extensional B ℓs ⦄
    → Extensional (A ⊻ B) (ℓr ⊔ ℓs)
  Extensional-⊻ {ℓs} ⦃ sa ⦄ .Pathᵉ (inxl a ¬b) (inxl a′ ¬b′) = Lift ℓs (Pathᵉ sa a a′)
  Extensional-⊻ {ℓr} ⦃ sb ⦄ .Pathᵉ (inxr b ¬a) (inxr b′ ¬a′) = Lift ℓr (Pathᵉ sb b b′)
  Extensional-⊻ .Pathᵉ _ _  = ⊥
  Extensional-⊻ ⦃ sa ⦄ .reflᵉ (inxl a ¬b) = lift (sa .reflᵉ a)
  Extensional-⊻ ⦃ sb ⦄ .reflᵉ (inxr b ¬a) = lift (sb .reflᵉ b)
  Extensional-⊻ ⦃ sa ⦄ .idsᵉ .to-path {inxl a ¬b} {inxl a′ ¬b′} (lift p) = ap² inxl (sa .idsᵉ .to-path p) prop!
  Extensional-⊻ ⦃ sb ⦄ .idsᵉ .to-path {inxr b ¬a} {inxr b′ ¬a′} (lift p) = ap² inxr (sb .idsᵉ .to-path p) prop!
  Extensional-⊻ ⦃ sa ⦄ .idsᵉ .to-path-over {inxl a ¬b} {inxl a′ ¬b′} (lift p) = apᴾ (λ _ → lift) $ sa .idsᵉ .to-path-over p
  Extensional-⊻ ⦃ sb ⦄ .idsᵉ .to-path-over {inxr b ¬a} {inxr b′ ¬a′} (lift p) = apᴾ (λ _ → lift) $ sb .idsᵉ .to-path-over p

opaque
  code-is-of-hlevel : {s₁ s₂ : A ⊻ B} {n : HLevel}
                    → is-of-hlevel (2 + n) A
                    → is-of-hlevel (2 + n) B
                    → is-of-hlevel (1 + n) (Extensional-⊻ .Pathᵉ s₁ s₂)
  code-is-of-hlevel {s₁ = inxl a ¬b} {inxl a′ ¬b′} {n} ahl bhl = Lift-is-of-hlevel (suc n) (ahl a a′)
  code-is-of-hlevel {s₁ = inxl a ¬b} {inxr b  ¬a}  {n} ahl bhl = hlevel (suc n)
  code-is-of-hlevel {s₁ = inxr b ¬a} {inxl a  ¬b}  {n} ahl bhl = hlevel (suc n)
  code-is-of-hlevel {s₁ = inxr b ¬a} {inxr b′ ¬a′} {n} ahl bhl = Lift-is-of-hlevel (suc n) (bhl b b′)

  ⊻-is-of-hlevel : (n : HLevel)
                 → is-of-hlevel (1 + n) A
                 → is-of-hlevel (1 + n) B
                 → is-of-hlevel (1 + n) (A ⊻ B)
  ⊻-is-of-hlevel 0 A-pr B-pr (inxl a ¬b) (inxl a′ ¬b′) = ap² inxl (A-pr a a′) prop!
  ⊻-is-of-hlevel 0 A-pr B-pr (inxl a ¬b) (inxr b  ¬a)  = ⊥.rec (¬a a)
  ⊻-is-of-hlevel 0 A-pr B-pr (inxr b ¬a) (inxl a  ¬b)  = ⊥.rec (¬b b)
  ⊻-is-of-hlevel 0 A-pr B-pr (inxr b ¬a) (inxr b′ ¬a′) = ap² inxr (B-pr b b′) prop!
  ⊻-is-of-hlevel (suc n) ahl bhl s₁ s₂ =
    ≃→is-of-hlevel (1 + n) (identity-system-gives-path (Extensional-⊻ .idsᵉ) ⁻¹)
      (code-is-of-hlevel {s₁ = s₁} {s₂ = s₂} ahl bhl)

  both-contr→¬⊻ : is-contr A → is-contr B → ¬ A ⊻ B
  both-contr→¬⊻ Ac Bc (inxl a ¬b) = ¬b (Bc .fst)
  both-contr→¬⊻ Ac Bc (inxr b ¬a) = ¬a (Ac .fst)

inxl-inj : {a a′ : A} {¬b ¬b′ : ¬ B} → inxl {B = B} a ¬b ＝ inxl a′ ¬b′ → a ＝ a′
inxl-inj {A} {a} = ap [ (λ a _ → a) , (λ _ _ → a) ]ₓ

inxr-inj : {b b′ : B} {¬a ¬a′ : ¬ A} → inxr {A = A} b ¬a ＝ inxr b′ ¬a′ → b ＝ b′
inxr-inj {B} {b} = ap [ (λ _ _ → b) , (λ b _ → b) ]ₓ

inxl-cancellable : {A : Type ℓᵃ} {B : Type ℓᵇ} {¬b : ¬ B} → Cancellable {A = A} {B = A ⊻ B} (λ a → inxl a ¬b)
inxl-cancellable = identity-system-gives-path (Extensional-⊻ .idsᵉ) ⁻¹ ∙ lift≃id

inxl-is-embedding : {A : Type ℓᵃ} {B : Type ℓᵇ} {¬b : ¬ B} → is-embedding {A = A} {B = A ⊻ B} (λ a → inxl a ¬b)
inxl-is-embedding = cancellable→is-embedding inxl-cancellable

inxr-cancellable : {A : Type ℓᵃ} {B : Type ℓᵇ} {¬a : ¬ A} → Cancellable {A = B} {B = A ⊻ B} (λ b → inxr b ¬a)
inxr-cancellable = identity-system-gives-path (Extensional-⊻ .idsᵉ) ⁻¹ ∙ lift≃id

inxr-is-embedding : {A : Type ℓᵃ} {B : Type ℓᵇ} {¬a : ¬ A} → is-embedding {A = B} {B = A ⊻ B} (λ b → inxr b ¬a)
inxr-is-embedding = cancellable→is-embedding inxr-cancellable

instance
  Reflects-inxl≠inxr : {a : A} {b : B} {¬a : ¬ A} {¬b : ¬ B} → Reflects (inxl a ¬b ＝ inxr b ¬a) false
  Reflects-inxl≠inxr = ofⁿ (λ p → ¬-so-false (subst So (ap is-inxl? p) oh))

  Reflects-inxr≠inxl : {a : A} {b : B} {¬a : ¬ A} {¬b : ¬ B} → Reflects (inxr b ¬a ＝ inxl a ¬b) false
  Reflects-inxr≠inxl = ofⁿ (λ p → ¬-so-false (subst So (ap is-inxr? p) oh))

  Reflects-inxl=inxl
    : {a a′ : A} {¬b ¬b′ : ¬ B}
    → ⦃ Reflects (Path A a a′) x ⦄ → Reflects (Path (A ⊻ B) (inxl a ¬b) (inxl a′ ¬b′)) x
  Reflects-inxl=inxl = Reflects.dmap (λ p → ap² inxl p prop!) (contra inxl-inj) auto

  Reflects-inxr=inxr
    : {b b′ : B} {¬a ¬a′ : ¬ A}
    → ⦃ Reflects (Path B b b′) x ⦄ → Reflects (Path (A ⊻ B) (inxr b ¬a) (inxr b′ ¬a′)) x
  Reflects-inxr=inxr = Reflects.dmap (λ p → ap² inxr p prop!) (contra inxr-inj) auto

  ⊻-is-discrete : ⦃ _ : is-discrete A ⦄ ⦃ _ : is-discrete B ⦄ → is-discrete (A ⊻ B)
  ⊻-is-discrete {x = inxl a ¬b} {inxl a′ ¬b′} = a =? a′ because auto
  ⊻-is-discrete {x = inxl a ¬b} {inxr b  ¬a}  = false because auto
  ⊻-is-discrete {x = inxr b ¬a} {inxl a  ¬b}  = false because auto
  ⊻-is-discrete {x = inxr b ¬a} {inxr b′ ¬a′} = b =? b′ because auto

opaque
  inxl≠inxr : {a : A} {¬b : ¬ B} {¬a : ¬ A} {b : B} → inxl a ¬b ≠ inxr b ¬a
  inxl≠inxr = false!

opaque
  inxr≠inxl : {a : A} {¬b : ¬ B} {¬a : ¬ A} {b : B} → inxr b ¬a ≠ inxl a ¬b
  inxr≠inxl = false!

instance opaque
  H-Level-⊻
    : ∀ {n} → ⦃ n ≥ʰ 1 ⦄ → ⦃ A-hl : H-Level n A ⦄ → ⦃ B-hl : H-Level n B ⦄
    → H-Level n (A ⊻ B)
  H-Level-⊻ {n} ⦃ s≤ʰs _ ⦄ .H-Level.has-of-hlevel = ⊻-is-of-hlevel _ (hlevel n) (hlevel n)
  {-# OVERLAPS H-Level-⊻ #-}
