{-# OPTIONS --safe #-}
module Truncation.Propositional.Base where

open import Foundations.Base
open import Foundations.HLevel.Base

data ∥_∥₁ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₁    : A → ∥ A ∥₁
  squash₁ : (x y : ∥ A ∥₁) → x ＝ y

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

opaque
  unfolding is-of-hlevel
  rec : is-prop B → (A → B) → ∥ A ∥₁ → B
  rec B-prop f ∣ x ∣₁ = f x
  rec B-prop f (squash₁ x y i) = B-prop (rec B-prop f x) (rec B-prop f y) i

  instance
    ∥-∥₁-is-prop : is-prop ∥ A ∥₁
    ∥-∥₁-is-prop = squash₁

map : (A → B) → (∥ A ∥₁ → ∥ B ∥₁)
map f = rec ∥-∥₁-is-prop (∣_∣₁ ∘ f)

proj : (A-prop : is-prop A) → ∥ A ∥₁ → A
proj A-prop = rec A-prop id

elim : {P : ∥ A ∥₁ → Type ℓ′}
     → Π[ x ꞉ ∥ A ∥₁ ] is-prop (P x)
     → Π[ x ꞉   A    ] P ∣ x ∣₁
     → Π[ x ꞉ ∥ A ∥₁ ] P   x
elim pprop incc ∣ x ∣₁ = incc x
elim pprop incc (squash₁ x y i) =
  is-prop→pathP (λ j → pprop (squash₁ x y j)) (elim pprop incc x)
                                              (elim pprop incc y)
                                              i


-- Mere existence

∃ : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃ A B = ∥ Σ[ a ꞉ A ] B a ∥₁

infix 2 ∃-syntax

∃-syntax : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃-syntax = ∃

syntax ∃-syntax A (λ x → B) = ∃[ x ꞉ A ] B


image : (A → B) → Type _
image {A} {B} f = Σ[ b ꞉ B ] ∃[ a ꞉ A ] (f a ＝ b)
