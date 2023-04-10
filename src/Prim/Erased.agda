{-# OPTIONS --safe #-}
module Prim.Erased where

open import Prim.Type
open import Prim.Interval
open import Prim.Kan

record Erased {ℓ} (@0 A : Type ℓ) : Type ℓ where
  constructor [_]
  field @0 erased : A
open Erased public

private variable
  ℓ ℓ′ : Level
  @0 A : Type ℓ
  @0 B : Type ℓ′
  @0 x y : A

[]-cong : Erased (x ＝ y) → ([ x ] ＝ [ y ])
[]-cong [ p ] = λ i → [ p i ]

substᴱ : (B : @0 A → Type ℓ′) → (@0 p : x ＝ y) → B x → B y
substᴱ B p = transport (λ i → B (p i))
-- substᴱ B p = subst (λ z → B (z .erased)) ([]-cong [ p ])
