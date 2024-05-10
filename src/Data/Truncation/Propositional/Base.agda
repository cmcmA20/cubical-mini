{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Base where

open import Meta.Prelude

open import Data.Sum.Base
  using (_⊎_)

data ∥_∥₁ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₁    : A → ∥ A ∥₁
  squash₁ : is-prop ∥ A ∥₁

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

elim : {A : Type ℓ} {P : ∥ A ∥₁ → Type ℓ′}
     → Π[ x ꞉ ∥ A ∥₁ ] is-prop (P x)
     → Π[ x ꞉   A    ] P ∣ x ∣₁
     → Π[ x ꞉ ∥ A ∥₁ ] P   x
elim P-prop incc ∣ x ∣₁ = incc x
elim P-prop incc (squash₁ x y i) =
  is-prop→pathᴾ (λ j → P-prop (squash₁ x y j)) (elim P-prop incc x)
                                               (elim P-prop incc y)
                                               i


-- Mere existence

∃ : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃ A B = ∥ Σ[ B ] ∥₁

infixr 6 ∃-syntax-und

∃-syntax-und
  : ⦃ _ : Underlying A ⦄ (X : A) (F : ⌞ X ⌟⁰ → Type ℓ′)
  → Type _
∃-syntax-und X F = ∃ ⌞ X ⌟⁰ F

syntax ∃-syntax-und X (λ x → F) = ∃[ x ꞉ X ] F

Existential₁ⁿ : Variadic-binding¹
Existential₁ⁿ = ∥_∥₁ ∘ Existentialⁿ

infixr 6 ∃[_]
macro ∃[_] = quantifier-macro (quote Existential₁ⁿ)


-- Mere disjunction
infixr 7 _⊎₁_
_⊎₁_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
_⊎₁_ = mapⁿ 2 ∥_∥₁ _⊎_

Sum₁ⁿ : Variadic²
Sum₁ⁿ {arity} P Q = mapⁿ arity ∥_∥₁ (Sumⁿ P Q)

infixr 7 _⊎̇₁_
macro _⊎̇₁_ = binop-macro (quote Sum₁ⁿ)


fibre₁ : {A : Type ℓ} {B : Type ℓ′} (f : A → B) (y : B) → Type (ℓ ⊔ ℓ′)
fibre₁ = mapⁿ 2 ∥_∥₁ fibre

Im : (A → B) → Type _
Im f = Σ[ fibre₁ f ]


-- Automation

instance
  Inductive-∥-∥₁
    : ∀ {ℓ ℓ′ ℓm} {A : Type ℓ} {P : ∥ A ∥₁ → Type ℓ′}
      ⦃ i : Inductive (∀ x → P ∣ x ∣₁) ℓm ⦄
    → ⦃ pr : ∀ {x} → H-Level 1 (P x) ⦄
    → Inductive (∀ x → P x) ℓm
  Inductive-∥-∥₁ ⦃ i ⦄ .Inductive.methods = i .Inductive.methods
  Inductive-∥-∥₁ ⦃ i ⦄ .Inductive.from f = elim (λ _ → hlevel 1) (i .Inductive.from f)

proj!
  : ⦃ A-prop : H-Level 1 A ⦄
  → ∥ A ∥₁ → A
proj! = rec! id
