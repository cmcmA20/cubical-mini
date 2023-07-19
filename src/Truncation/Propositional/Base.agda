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

rec : is-prop B → (A → B) → ∥ A ∥₁ → B
rec B-prop f ∣ x ∣₁ = f x
rec B-prop f (squash₁ x y i) = is-prop-β B-prop (rec B-prop f x) (rec B-prop f y) i

instance
  ∥-∥₁-is-prop : is-prop ∥ A ∥₁
  ∥-∥₁-is-prop = is-prop-η squash₁

∥-∥₁-is-of-hlevel : (n : HLevel) → is-of-hlevel (suc n) ∥ A ∥₁
∥-∥₁-is-of-hlevel n = is-of-hlevel-+-left 1 n ∥-∥₁-is-prop


map : (A → B) → (∥ A ∥₁ → ∥ B ∥₁)
map f = rec ∥-∥₁-is-prop (∣_∣₁ ∘ f)

proj : (A-prop : is-prop A) → ∥ A ∥₁ → A
proj A-prop = rec A-prop id

elim : {P : ∥ A ∥₁ → Type ℓ′}
     → Π[ x ꞉ ∥ A ∥₁ ] is-prop (P x)
     → Π[ x ꞉   A    ] P ∣ x ∣₁
     → Π[ x ꞉ ∥ A ∥₁ ] P   x
elim P-prop incc ∣ x ∣₁ = incc x
elim P-prop incc (squash₁ x y i) =
  is-prop→pathP (λ j → P-prop (squash₁ x y j)) (elim P-prop incc x)
                                               (elim P-prop incc y)
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
