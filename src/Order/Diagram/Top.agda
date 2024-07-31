{-# OPTIONS --safe #-}
module Order.Diagram.Top where

open import Categories.Prelude
open import Categories.Diagram.Terminal

open import Order.Base
open import Order.Category
open import Order.Diagram.Glb

module _ {o ℓ} (P : Poset o ℓ) where
  open import Order.Reasoning P

  open is-glb
  open Glb

  is-top : Ob → Type _
  is-top top = ∀ x → x ≤ top

  record Top : Type (o ⊔ ℓ) where
    field
      top : Ob
      has-top : is-top top

    ! : ∀ {x} → x ≤ top
    ! = has-top _

  unquoteDecl Top-Iso = declare-record-iso Top-Iso (quote Top)

  is-top→is-glb : ∀ {glb} {f : ⊥ → _} → is-top glb → is-glb P f glb
  is-top→is-glb is-top .greatest x _ = is-top x

  is-glb→is-top : ∀ {glb} {f : ⊥ → _} → is-glb P f glb → is-top glb
  is-glb→is-top glb x = glb .greatest x λ ()

  is-top≃is-glb : ∀ {glb} {f} → is-top glb ≃ is-glb P f glb
  is-top≃is-glb = is-top→is-glb , biimp-is-equiv! _ is-glb→is-top

  is-top-is-prop : ∀ x → is-prop (is-top x)
  is-top-is-prop _ = hlevel 1

  top-unique : ∀ {x y} → is-top x → is-top y → x ＝ y
  top-unique p q = ≤-antisym (q _) (p _)

  Top-is-prop : is-prop Top
  Top-is-prop = ≅→is-of-hlevel 1 Top-Iso λ x y → top-unique (x .snd) (y .snd) ,ₚ prop!

  instance
    H-Level-Top
      : ∀ {n} ⦃ _ : 1 ≤ʰ n ⦄
      → H-Level n Top
    H-Level-Top ⦃ s≤ʰs _ ⦄ = hlevel-basic-instance 1 Top-is-prop

  Top→Glb : ∀ {f : ⊥ → _} → Top → Glb P f
  Top→Glb top .Glb.glb = Top.top top
  Top→Glb top .Glb.has-glb = is-top→is-glb (Top.has-top top)

  Glb→Top : ∀ {f : ⊥ → _} → Glb P f → Top
  Glb→Top glb .Top.top = Glb.glb glb
  Glb→Top glb .Top.has-top = is-glb→is-top (Glb.has-glb glb)

  Top≃Glb : ∀ {f} → Top ≃ Glb P f
  Top≃Glb = Top→Glb , biimp-is-equiv! _ Glb→Top

  is-top→is-terminal : ∀ {x} → is-top x → is-terminal (poset→precategory P) x
  is-top→is-terminal is-top x .fst = is-top x
  is-top→is-terminal is-top x .snd _ = ≤-thin _ _

  is-terminal→is-top : ∀ {x} → is-terminal (poset→precategory P) x → is-top x
  is-terminal→is-top terminal x = terminal x .fst

  is-top≃is-terminal : ∀{x} → is-top x ≃ is-terminal (poset→precategory P) x
  is-top≃is-terminal = is-top→is-terminal , biimp-is-equiv! _ is-terminal→is-top


instance
  ⊤-Top : ∀ {o ℓ} {P : Poset o ℓ} ⦃ b : Top P ⦄ → ⊤-notation ⌞ P ⌟
  ⊤-Top ⦃ b ⦄ .⊤ = b .Top.top
