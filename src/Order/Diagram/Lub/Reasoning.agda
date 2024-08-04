{-# OPTIONS --safe #-}
open import Order.Base
open import Order.Diagram.Lub

module Order.Diagram.Lub.Reasoning
  {o ℓ} (P : Poset o ℓ) {ℓ′} ⦃ hl : Has-lubs P ℓ′ ⦄
  where

open import Categories.Prelude

open import Order.Reasoning P
open Lub

lubs : {I : Type ℓ′} (F : I → Ob) → Lub P F
lubs F = hl {F = F}

module lubs {I} {F} = Lub (lubs {I} F)
open lubs using
  ( lub
  ; fam≤lub
  ; least
  ) public

module sups = lubs
open sups renaming
  ( lub     to sup
  ; fam≤lub to fam≤sup
  ; least   to sup-universal
  ) public

-- TODO
