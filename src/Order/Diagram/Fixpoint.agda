{-# OPTIONS --safe #-}
module Order.Diagram.Fixpoint where

open import Categories.Prelude
open import Order.Base
import Order.Reasoning

module _ {o ℓ} (P : Poset o ℓ) where
  open Order.Reasoning P

  record is-lfp (f : P ⇒ P) (x : Ob) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      fixed : f # x ＝ x
      least : (y : Ob) → f # y ＝ y → x ≤ y

  record LFP (f : P ⇒ P) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      fixpoint : Ob
      has-lfp  : is-lfp f fixpoint

unquoteDecl H-Level-is-lfp = declare-record-hlevel 1 H-Level-is-lfp (quote is-lfp)
unquoteDecl LFP-Iso = declare-record-iso LFP-Iso (quote LFP)

module _ {o ℓ} {P : Poset o ℓ} where
  open Order.Reasoning P
  open is-lfp

  opaque
    lfp-unique : ∀{f x y} → is-lfp P f x → is-lfp P f y → x ＝ y
    lfp-unique xl yl = ≤-antisym (xl .least _ (yl .fixed)) (yl .least _ (xl .fixed))

    LFP-is-prop : ∀{f} → is-prop (LFP P f)
    LFP-is-prop = ≅→is-of-hlevel 1 LFP-Iso (λ xl yl → lfp-unique (xl .snd) (yl .snd) ,ₚ prop!)

  instance
    H-Level-LFP
      : ∀ {f n} ⦃ _ : 1 ≤ʰ n ⦄
      → H-Level n (LFP P f)
    H-Level-LFP ⦃ s≤ʰs _ ⦄ = hlevel-basic-instance 1 LFP-is-prop
