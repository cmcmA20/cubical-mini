{-# OPTIONS --safe #-}
module Truncation.Set.Base where

open import Foundations.Base
open import Foundations.HLevel.Base

data ∥_∥₂ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₂    : A → ∥ A ∥₂
  squash₂ : (x y : ∥ A ∥₂) (p q : x ＝ y) → p ＝ q

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

rec : is-set B → (A → B) → ∥ A ∥₂ → B
rec _ f ∣ x ∣₂ = f x
rec B-set f (squash₂ x y p q i j) =
  is-set-β B-set (go x) (go y) (λ k → go (p k)) (λ k → go (q k)) i j where
    go : ∥ _ ∥₂ → _
    go = rec B-set f

instance
  ∥-∥₂-is-set : is-set ∥ A ∥₂
  ∥-∥₂-is-set = is-set-η squash₂

∥-∥₂-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) ∥ A ∥₂
∥-∥₂-is-of-hlevel n = is-of-hlevel-+-left 2 n ∥-∥₂-is-set

map : (A → B) → (∥ A ∥₂ → ∥ B ∥₂)
map f = rec ∥-∥₂-is-set (∣_∣₂ ∘ f)

proj : (A-set : is-set A) → ∥ A ∥₂ → A
proj A-set = rec A-set id

elim : {P : ∥ A ∥₂ → Type ℓ′}
     → Π[ x ꞉ ∥ A ∥₂ ] is-set (P x)
     → Π[ x ꞉   A    ] P ∣ x ∣₂
     → Π[ x ꞉ ∥ A ∥₂ ] P   x
elim _ incc ∣ x ∣₂ = incc x
elim P-set incc (squash₂ x y p q i j) =
  is-set→squareP (λ k l → P-set (squash₂ x y p q k l))
    (λ _ → go x) (λ k → go (p k)) (λ k → go (q k)) (λ _ → go y) i j
    where go = elim P-set incc
