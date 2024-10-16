{-# OPTIONS --safe #-}
module Foundations.Notation.Commutativity where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Composition
open import Foundations.Notation.Duality

-- A ---|--> C
-- |         |
-- |         |
-- v         v
-- B ---|--> D

-- most generic square
-- module _
--   {ℓa ℓb ℓc ℓd ℓf ℓg ℓh ℓk ℓs : Level}
--   {A : 𝒰 ℓa} {B : 𝒰 ℓb} {C : 𝒰 ℓc} {D : 𝒰 ℓd}
--   (F : A → B → 𝒰 ℓf) (G : A → C → 𝒰 ℓg)
--   (H : C → D → 𝒰 ℓh) (K : B → D → 𝒰 ℓk)
--   (S : ∀{a b c d} (f : F a b) (g : G a c) (h : H c d) (k : K b d) → 𝒰 ℓs) where

-- damn, generalized commutativity got hands
-- what should it be, naturality?

module _ {ℓ} (A : 𝒰 ℓ) where
  Commutativity : (t : A → A → A) (x y : A) → 𝒰 ℓ
  Commutativity t x y = t y x ＝ t x y

  record Comm ⦃ t : Has-binary-op A ⦄ : 𝒰 ℓ where
    no-eta-equality
    field <>-comm : ∀ x y → Commutativity (t ._<>_) x y

open Comm ⦃ ... ⦄ public
