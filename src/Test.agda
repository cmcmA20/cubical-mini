{-# OPTIONS --safe #-}
module Test where

open import Prelude

open import Data.Bool
open import Data.Fin.Inductive as Fin
open import Data.Fin.Computational as Finᶜ
  renaming (Fin to Finᶜ; fzero to fzeroᶜ; fsuc to fsucᶜ)
open import Data.Nat
open import Data.Vec.Inductive as Vec

private variable @0 m n : ℕ

-- Computational fin

-- constant index
_ : substₚ (λ n → Finᶜ n) refl (fzeroᶜ {4}) ＝ 0
_ = refl -- GOOD

_ : subst {B = λ n → Finᶜ n} refl (fzeroᶜ {4}) ＝ 0
_ = refl

-- mixed index
module _ (@0 n : ℕ) (p : 4 ＝ 2 + n) where private
  _ : substₚ (λ n → Finᶜ n) p 0 ＝ 0
  _ = refl -- GOOD

  _ : subst {B = (λ n → Finᶜ n)} p 0 ＝ 0
  _ = refl

-- variable index
module _ (n : ℕ) (p : 2 ＝ n) where private
  k : Finᶜ n
  k = substₚ (λ n → Finᶜ n) p 0

  _ : substₚ (λ n → Finᶜ n) (p ⁻¹) k ＝ 0
  _ = refl -- GOOD

  k′ : Finᶜ n
  k′ = subst {B = λ n → Finᶜ n} p 0

  _ : subst {B = (λ n → Finᶜ n)} (p ⁻¹) k′ ＝ 0
  _ = refl


-- Inductive fin

-- constant index
_ : substₚ (λ n → Fin n) refl (fzero {4}) ＝ 0
_ = transport-refl _ -- NOT GOOD

_ : subst {B = λ n → Fin n} refl (fzero {n = 4}) ＝ 0
_ = refl

-- mixed index
module _ (n : ℕ) (p : 4 ＝ 2 + n) where
  _ : substₚ (λ n → Fin n) p 1 ＝ 1
  _ = {!!} -- SUCKS ASS

  _ : subst {B = λ n → Fin n} p 1 ＝ 1
  _ = refl

-- variable index
module _ (n : ℕ) (p : 2 ＝ n) where private
  k : Fin n
  k = substₚ (λ n → Fin n) p 0

  _ : substₚ (λ n → Fin n) (p ⁻¹) k ＝ 0
  _ = {!!} -- SUCKS ASS

  k′ : Fin n
  k′ = subst {B = λ n → Fin n} p 0

  @0 _ : subst {B = λ n → Fin n} (p ⁻¹) k′ ＝ 0
  _ = is-transport-system.subst-coh fin-transport-system _ k′ .erased
    ∙ ap {x = k′} {y = substₚ (λ n₁ → Fin n₁) p 0} (substₚ (λ n → Fin n) (p ⁻¹))
        (is-transport-system.subst-coh fin-transport-system _ 0 .erased)
    ∙ subst⁻-subst (λ n → Fin n) p 0 -- SUCKS ASS


-- Inductive vec

-- constant index
xs₁ : Vec Bool 2
xs₁ = [ false , true ]

_ : substₚ (λ n → Vec Bool n) refl xs₁ ＝ xs₁
_ = transport-refl _ -- NOT GOOD

_ : subst {B = λ n → Vec Bool n} refl xs₁ ＝ xs₁
_ = refl

-- mixed index
module _ (n : ℕ) (p : 1 ＝ 1 + n) where private
  xs₂ : Vec Bool (1 + n)
  xs₂ = substₚ (λ m → Vec Bool m) p [ true ]

  _ : xs₂ ＝ true ∷ substₚ (λ m → Vec Bool m) (suc-inj p) []
  _ = {!!} -- SUCKS ASS

  hd : Bool
  hd = head (substₚ (λ m → Vec Bool m) (p ⁻¹) xs₂)

  _ : hd ＝ true
  _ = {!!} -- SUCKS ASS

  xs₂′ : Vec Bool (1 + n)
  xs₂′ = subst {B = λ m → Vec Bool m} p [ true ]

  _ : xs₂′ ＝ true ∷ subst {B = λ m → Vec Bool m} (suc-inj p) []
  _ = refl

  hd′ : Bool
  hd′ = head (subst {B = λ m → Vec Bool m} (p ⁻¹) xs₂′)

  _ : hd′ ＝ true
  _ = refl

-- variable index
module _ (n : ℕ) (p : 2 ＝ n) where private
  xs₂ : Vec Bool n
  xs₂ = substₚ (λ m → Vec Bool m) p xs₁

  hd : Bool
  hd = head (substₚ (λ m → Vec Bool m) (p ⁻¹) xs₂)

  _ : hd ＝ true
  _ = {!!} -- SUCKS ASS

  xs₂′ : Vec Bool n
  xs₂′ = subst {B = λ m → Vec Bool m} p xs₁

  hd′ : Bool
  hd′ = head (subst {B = λ m → Vec Bool m} (p ⁻¹) xs₂′)

  @0 _ : hd′ ＝ true
  _ = {!!} -- SUCKS ASS
