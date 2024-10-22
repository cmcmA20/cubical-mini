{-# OPTIONS --safe #-}
open import Cat.Prelude
open import Order.Base
open import Order.Lattice

module Order.Lattice.Reasoning
  {o ℓ} {P : Poset o ℓ} (L : is-lattice P) where

open Poset P
open is-lattice L public

private variable x y : Ob

opaque
  absorb-∩-∪-l : x ∩ (x ∪ y) ＝ x
  absorb-∩-∪-l = order→∩ l≤∪

  absorb-∩-∪-r : (x ∩ y) ∪ y ＝ y
  absorb-∩-∪-r = order→∪ ∩≤r

  absorb-∪-∩-l : x ∪ (x ∩ y) ＝ x
  absorb-∪-∩-l = ∪-comm ∙ order→∪ ∩≤l

  absorb-∪-∩-r : (x ∪ y) ∩ y ＝ y
  absorb-∪-∩-r = ∩-comm ∙ order→∩ r≤∪
