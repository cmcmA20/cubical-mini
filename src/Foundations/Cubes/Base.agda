{-# OPTIONS --safe #-}
module Foundations.Cubes.Base where

open import Foundations.Prelude

private variable
  ℓ : Level
  A : Type ℓ

-- Higher cube types

SquareP
  : (A : I → I → Type ℓ)
    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : ＜ a₀₀ ／ (λ j → A i0 j) ＼ a₀₁ ＞)
    {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : ＜ a₁₀ ／ (λ j → A i1 j) ＼ a₁₁ ＞)
    (a₋₀ : ＜ a₀₀ ／ (λ i → A i i0) ＼ a₁₀ ＞) (a₋₁ : ＜ a₀₁ ／ (λ i → A i i1) ＼ a₁₁ ＞)
  → Type ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = ＜ a₀₋ ／ (λ i → ＜ a₋₀ i ／ (λ j → A i j) ＼ a₋₁ i ＞) ＼ a₁₋ ＞

-- Cube :
--   {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ＝ a₀₀₁}
--   {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ＝ a₀₁₁}
--   {a₀₋₀ : a₀₀₀ ＝ a₀₁₀} {a₀₋₁ : a₀₀₁ ＝ a₀₁₁}
--   (a₀₋₋ : Square a₀₀₋ a₀₋₀ a₀₋₁ a₀₁₋)
--   {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ＝ a₁₀₁}
--   {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ＝ a₁₁₁}
--   {a₁₋₀ : a₁₀₀ ＝ a₁₁₀} {a₁₋₁ : a₁₀₁ ＝ a₁₁₁}
--   (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--   {a₋₀₀ : a₀₀₀ ＝ a₁₀₀} {a₋₀₁ : a₀₀₁ ＝ a₁₀₁}
--   (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--   {a₋₁₀ : a₀₁₀ ＝ a₁₁₀} {a₋₁₁ : a₀₁₁ ＝ a₁₁₁}
--   (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--   (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--   (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--   → Type _
-- Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
--   PathP (λ i → Square (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i)) a₀₋₋ a₁₋₋

-- Alternative (equivalent) definitions of hlevel n that give fillers for n-cubes instead of n-globes

-- isSet' : Type ℓ → Type ℓ
-- isSet' A =
--   {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ＝ a₀₁)
--   {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ＝ a₁₁)
--   (a₋₀ : a₀₀ ＝ a₁₀) (a₋₁ : a₀₁ ＝ a₁₁)
--   → Square a₀₋ a₁₋ a₋₀ a₋₁

-- isSet→isSet' : isSet A → isSet' A
-- isSet→isSet' Aset _ _ _ _ = toPathP (Aset _ _ _ _)

-- isSet'→isSet : isSet' A → isSet A
-- isSet'→isSet Aset' x y p q = Aset' p q refl refl

-- is-prop→is-set' : is-prop A → is-set′ A
-- is-prop→is-set' h {a} p q r s i j = ?
--   hcomp (λ k → λ { (i = i0) → h a (p j) k
--                  ; (i = i1) → h a (q j) k
--                  ; (j = i0) → h a (r i) k
--                  ; (j = i1) → h a (s i) k}) a

-- isGroupoid' : Type ℓ → Type ℓ
-- isGroupoid' A =
--   {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ＝ a₀₀₁}
--   {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ＝ a₀₁₁}
--   {a₀₋₀ : a₀₀₀ ＝ a₀₁₀} {a₀₋₁ : a₀₀₁ ＝ a₀₁₁}
--   (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--   {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ＝ a₁₀₁}
--   {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ＝ a₁₁₁}
--   {a₁₋₀ : a₁₀₀ ＝ a₁₁₀} {a₁₋₁ : a₁₀₁ ＝ a₁₁₁}
--   (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--   {a₋₀₀ : a₀₀₀ ＝ a₁₀₀} {a₋₀₁ : a₀₀₁ ＝ a₁₀₁}
--   (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--   {a₋₁₀ : a₀₁₀ ＝ a₁₁₀} {a₋₁₁ : a₀₁₁ ＝ a₁₁₁}
--   (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--   (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--   (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--   → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
