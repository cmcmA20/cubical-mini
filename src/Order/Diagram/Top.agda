{-# OPTIONS --safe #-}
open import Categories.Diagram.Terminal
open import Categories.Prelude

open import Data.Empty

open import Order.Diagram.Glb
open import Order.Base
open import Order.Category

import Order.Reasoning

module Order.Diagram.Top {o ℓ} (P : Poset o ℓ) where

open Order.Reasoning P

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

is-top→is-glb : ∀ {glb} {f : ⊥ → _} → is-top glb → is-glb P f glb
is-top→is-glb is-top .greatest x _ = is-top x

is-glb→is-top : ∀ {glb} {f : ⊥ → _} → is-glb P f glb → is-top glb
is-glb→is-top glb x = glb .greatest x λ ()

is-top-is-prop : ∀ x → is-prop (is-top x)
is-top-is-prop _ = hlevel 1

top-unique : ∀ {x y} → is-top x → is-top y → x ＝ y
top-unique p q = ≤-antisym (q _) (p _)

Top-is-prop : is-prop Top
Top-is-prop p q i .Top.top =
  top-unique (Top.has-top p) (Top.has-top q) i
Top-is-prop p q i .Top.has-top =
  is-prop→pathᴾ
    (λ i → is-top-is-prop (top-unique (Top.has-top p) (Top.has-top q) i))
    (Top.has-top p) (Top.has-top q) i

instance
  H-Level-Top
    : ∀ {n}
    → H-Level (suc n) Top
  H-Level-Top = hlevel-basic-instance 1 Top-is-prop

Top→Glb : ∀ {f : ⊥ → _} → Top → Glb P f
Top→Glb top .Glb.glb = Top.top top
Top→Glb top .Glb.has-glb = is-top→is-glb (Top.has-top top)

Glb→Top : ∀ {f : ⊥ → _} → Glb P f → Top
Glb→Top glb .Top.top = Glb.glb glb
Glb→Top glb .Top.has-top = is-glb→is-top (Glb.has-glb glb)

is-top≃is-glb : ∀ {glb} {f} → is-equiv (is-top→is-glb {glb} {f})
is-top≃is-glb = biimp-is-equiv! _ is-glb→is-top

Top≃Glb : ∀ {f} → is-equiv (Top→Glb {f})
Top≃Glb = biimp-is-equiv! _ Glb→Top

is-top→terminal : ∀ {x} → is-top x → is-terminal (poset→precategory P) x
is-top→terminal is-top x .fst = is-top x
is-top→terminal is-top x .snd _ = ≤-thin _ _

terminal→is-top : ∀ {x} → is-terminal (poset→precategory P) x → is-top x
terminal→is-top terminal x = terminal x .fst
