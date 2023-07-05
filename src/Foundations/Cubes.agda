{-# OPTIONS --safe #-}
module Foundations.Cubes where

open import Foundations.Base

private variable
  ℓ : Level
  A : Type ℓ

-- Higher cube types

SquareP
  : (A : I → I → Type ℓ)
    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : ＜ a₀₀ ／ (λ j → A i0 j) ＼ a₀₁ ＞)
    {a₁₀ : A i1 i0} (a₋₀ : ＜ a₀₀ ／ (λ i → A i i0) ＼ a₁₀ ＞)
    {a₁₁ : A i1 i1} (a₁₋ : ＜ a₁₀ ／ (λ j → A i1 j) ＼ a₁₁ ＞)
    (a₋₁ : ＜ a₀₁ ／ (λ i → A i i1) ＼ a₁₁ ＞)
  → Type ℓ
SquareP A a₀₋ a₋₀ a₁₋ a₋₁ = ＜ a₀₋ ／ (λ i → ＜ a₋₀ i ／ (λ j → A i j) ＼ a₋₁ i ＞) ＼ a₁₋ ＞

-- 3d unicode diagrams are beyond my ability, sorry
Cube
  : {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ＝ a₀₀₁}
    {a₀₁₀ : A} {a₀₋₀ : a₀₀₀ ＝ a₀₁₀}
    {a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ＝ a₀₁₁}
    {a₀₋₁ : a₀₀₁ ＝ a₀₁₁}
    (a₀₋₋ : Square a₀₀₋ a₀₋₀ a₀₁₋ a₀₋₁)
    {a₁₀₀ : A} {a₋₀₀ : a₀₀₀ ＝ a₁₀₀}
    {a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ＝ a₁₀₁}
    {a₋₀₁ : a₀₀₁ ＝ a₁₀₁}
    (a₋₀₋ : Square a₀₀₋ a₋₀₀ a₁₀₋ a₋₀₁)
    {a₁₁₀ : A} {a₁₋₀ : a₁₀₀ ＝ a₁₁₀}
    {a₋₁₀ : a₀₁₀ ＝ a₁₁₀}
    (a₋₋₀ : Square a₀₋₀ a₋₀₀ a₁₋₀ a₋₁₀)
    {a₁₁₁ : A} {a₁₋₁ : a₁₀₁ ＝ a₁₁₁}
    {a₁₁₋ : a₁₁₀ ＝ a₁₁₁}
    (a₁₋₋ : Square a₁₀₋ a₁₋₀ a₁₁₋ a₁₋₁)
    {a₋₁₁ : a₀₁₁ ＝ a₁₁₁}
    (a₋₁₋ : Square a₀₁₋ a₋₁₀ a₁₁₋ a₋₁₁)
    (a₋₋₁ : Square a₀₋₁ a₋₀₁ a₁₋₁ a₋₁₁)
  → Type (level-of-type A)
Cube a₀₋₋ a₋₀₋ a₋₋₀ a₁₋₋ a₋₁₋ a₋₋₁ =
  ＜ a₋₋₀ ／ (λ k → Square (a₀₋₋ k) (a₋₀₋ k) (a₁₋₋ k) (a₋₁₋ k)) ＼ a₋₋₁ ＞


-- Alternative (equivalent) definitions of hlevel n that give fillers for n-cubes instead of n-globes

is-set-□ : Type ℓ → Type ℓ
is-set-□ A =
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ＝ a₀₁)
  {a₁₀ : A} (a₋₀ : a₀₀ ＝ a₁₀)
  {a₁₁ : A} (a₁₋ : a₁₀ ＝ a₁₁)
  (a₋₁ : a₀₁ ＝ a₁₁) → Square a₀₋ a₋₀ a₁₋ a₋₁

opaque
  unfolding is-of-hlevel
  is-set→is-set-□ : is-set A → is-set-□ A
  is-set→is-set-□ A-set a₀₋ a₋₀ a₁₋ a₋₁ = to-pathP (A-set _ _ _ a₋₁)

  is-set-□→is-set : is-set-□ A → is-set A
  is-set-□→is-set A-set-□ _ _ p q = A-set-□ refl p refl q

  is-prop→is-set-□ : is-prop A → is-set-□ A
  is-prop→is-set-□ h {a₀₀} p q r s i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → h a₀₀ (q j) k
    k (i = i1) → h a₀₀ (s j) k
    k (j = i0) → h a₀₀ (p i) k
    k (j = i1) → h a₀₀ (r i) k
    k (k = i0) → a₀₀

-- TODO uncomment and fix?
-- is-groupoid-□ : Type ℓ → Type ℓ
-- is-groupoid-□ A =
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
