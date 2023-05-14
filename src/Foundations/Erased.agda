{-# OPTIONS --safe #-}
module Foundations.Erased where

open import Foundations.Type
open import Foundations.Prim.Interval
open import Foundations.Prim.Kan

record Erased {ℓ} (@0 A : Type ℓ) : Type ℓ where
  constructor [_]ᴱ
  field @0 erased : A
open Erased public

private variable
  ℓ ℓ′ : Level
  @0 A : Type ℓ
  @0 B : Type ℓ′
  @0 x y : A

instance
  Erased-inst : {A : Type ℓ} → ⦃ A ⦄ → Erased A
  Erased-inst ⦃ (a) ⦄ .erased = a

[]ᴱ-cong : Erased (x ＝ y) → ([ x ]ᴱ ＝ [ y ]ᴱ)
[]ᴱ-cong [ p ]ᴱ = λ i → [ p i ]ᴱ

substᴱ : (B : @0 A → Type ℓ′) → (@0 p : x ＝ y) → B x → B y
substᴱ B p = transport (λ i → B (p i))
-- substᴱ B p = subst (λ z → B (z .erased)) ([]ᴱ-cong [ p ]ᴱ)
