{-# OPTIONS --safe #-}
module Order.Diagram.Top where

open import Categories.Prelude
open import Categories.Diagram.Terminal

open import Order.Base
open import Order.Category
open import Order.Diagram.Glb
import Order.Reasoning

private variable o ℓ : Level

module _ (P : Poset o ℓ) where
  open Order.Reasoning P

  is-top : Ob → Type _
  is-top top = ∀ x → x ≤ top

  record Top : Type (o ⊔ ℓ) where
    field
      top     : Ob
      has-top : is-top top

    instance
      ⊤-Top : ⊤-notation Ob
      ⊤-Top .⊤ = top

    ! : ∀ {x} → x ≤ ⊤
    ! = has-top _

{-# DISPLAY Top.top = ⊤ #-}
unquoteDecl Top-Iso = declare-record-iso Top-Iso (quote Top)

module _ {P : Poset o ℓ} where
  open Order.Reasoning P

  is-top→is-glb : ∀ {glb} {f : ⊥ → _} → is-top P glb → is-glb P f glb
  is-top→is-glb is-top .is-glb.greatest x _ = is-top x

  is-glb→is-top : ∀ {glb} {f : ⊥ → _} → is-glb P f glb → is-top P glb
  is-glb→is-top glb x = glb .is-glb.greatest x λ ()

  is-top≃is-glb : ∀ {glb} {f} → is-top P glb ≃ is-glb P f glb
  is-top≃is-glb = is-top→is-glb , biimp-is-equiv! _ is-glb→is-top

  top-unique : ∀ {x y} → is-top P x → is-top P y → x ＝ y
  top-unique p q = ≤-antisym (q _) (p _)

  Top-is-prop : is-prop (Top P)
  Top-is-prop = ≅→is-of-hlevel 1 Top-Iso λ x y → top-unique (x .snd) (y .snd) ,ₚ prop!

  instance
    H-Level-Top
      : ∀ {n} ⦃ _ : 1 ≤ʰ n ⦄
      → H-Level n (Top P)
    H-Level-Top ⦃ s≤ʰs _ ⦄ = hlevel-basic-instance 1 Top-is-prop

  Top→Glb : ∀ {f : ⊥ → _} → Top P → Glb P f
  Top→Glb top .Glb.glb = Top.top top
  Top→Glb top .Glb.has-glb = is-top→is-glb (Top.has-top top)

  Glb→Top : ∀ {f : ⊥ → _} → Glb P f → Top P
  Glb→Top glb .Top.top = Glb.glb glb
  Glb→Top glb .Top.has-top = is-glb→is-top (Glb.has-glb glb)

  Top≃Glb : ∀ {f} → Top P ≃ Glb P f
  Top≃Glb = Top→Glb , biimp-is-equiv! _ Glb→Top

  is-top→is-terminal : ∀ {x} → is-top P x → is-terminal (poset→precategory P) x
  is-top→is-terminal is-top x .fst = is-top x
  is-top→is-terminal is-top x .snd _ = ≤-thin _ _

  is-terminal→is-top : ∀ {x} → is-terminal (poset→precategory P) x → is-top P x
  is-terminal→is-top terminal x = terminal x .fst

  is-top≃is-terminal : ∀{x} → is-top P x ≃ is-terminal (poset→precategory P) x
  is-top≃is-terminal = is-top→is-terminal , biimp-is-equiv! _ is-terminal→is-top
