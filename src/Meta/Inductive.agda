{-# OPTIONS --safe #-}
module Meta.Inductive where

open import Foundations.Prelude
  hiding (case_of_; case_return_of_)

open import Meta.Reflection.Base

record Inductive {ℓ} (A : Type ℓ) ℓm : Type (ℓ ⊔ ℓsuc ℓm) where
  field
    methods : Type ℓm
    from    : methods → A

open Inductive

private variable
  ℓ ℓ′ ℓ″ ℓm : Level
  A B C : Type ℓ
  P Q R : A → Type ℓ

instance
  Inductive-default : Inductive A (level-of-type A)
  Inductive-default .methods = _
  Inductive-default .from x  = x
  {-# INCOHERENT Inductive-default #-}

  Inductive-Π
    : ⦃ r : {x : A} → Inductive (P x) ℓm ⦄
    → Inductive (∀ x → P x) (level-of-type A ⊔ ℓm)
  Inductive-Π ⦃ r ⦄ .methods  = ∀ x → r {x} .methods
  Inductive-Π ⦃ r ⦄ .from f x = r .from (f x)
  {-# OVERLAPPABLE Inductive-Π #-}

  Inductive-Σ
    : ∀ {A : Type ℓ} {B : A → Type ℓ′} {C : (x : A) → B x → Type ℓ″}
    → ⦃ r : Inductive ((x : A) (y : B x) → C x y) ℓm ⦄
    → Inductive ((x : Σ A B) → C (x .fst) (x .snd)) ℓm
  Inductive-Σ ⦃ r ⦄ .methods        = r .methods
  Inductive-Σ ⦃ r ⦄ .from f (x , y) = r .from f x y

  Inductive-Lift
    : {B : Lift ℓ A → Type ℓ′}
    → ⦃ i : Inductive (∀ x → B (lift x)) ℓm ⦄
    → Inductive (∀ x → B x) ℓm
  Inductive-Lift ⦃ i ⦄ = record { from = λ f (lift x) → i .from f x }

  Inductive-≃ : {C : A ≃ B → Type ℓ″} → Inductive (∀ x → C x) _
  Inductive-≃ = Inductive-default
  {-# OVERLAPPING Inductive-≃ #-}


elim! : ⦃ r : Inductive (∀ x → P x) ℓm ⦄ → r .methods → ∀ x → P x
elim! ⦃ r ⦄ = r .from

rec! : ⦃ r : Inductive (A → B) ℓm ⦄ → r .methods → A → B
rec! ⦃ r ⦄ = r .from

case_return_of_
  : (x : A) (B : A → Type ℓ′)
    ⦃ r : Inductive (∀ x → B x) ℓm ⦄
    (f : r .methods) → B x
case x return P of f = elim! f x
{-# INLINE case_return_of_ #-}

case_of_
  : {B : Type ℓ′}
    ⦃ r : Inductive (A → B) ℓm ⦄
  → A → r .methods → B
case x of f = rec! f x
{-# INLINE case_of_ #-}
