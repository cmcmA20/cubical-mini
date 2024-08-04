{-# OPTIONS --safe #-}
open import Order.Base
open import Order.Diagram.Glb

module Order.Diagram.Glb.Reasoning
  {o ℓ} (P : Poset o ℓ) {ℓ′} ⦃ hl : Has-glbs P ℓ′ ⦄
  where

open import Categories.Prelude

open import Order.Reasoning P
open Glb

glbs : {I : Type ℓ′} (F : I → Ob) → Glb P F
glbs F = hl {F = F}

module glbs {I} {F} = Glb (glbs {I} F)
open glbs using
  ( glb
  ; glb≤fam
  ; greatest
  ) public

module infs = glbs
open infs renaming
  ( glb      to inf
  ; glb≤fam  to inf≤fam
  ; greatest to inf-universal
  ) public

-- TODO
