{-# OPTIONS --safe #-}
module Truncation.Propositional.Base where

open import Meta.Prelude

open import Data.Sum.Base
  using (_⊎_)

data ∥_∥₁ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₁    : A → ∥ A ∥₁
  squash₁ : (x y : ∥ A ∥₁) → x ＝ y

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″

instance opaque
  H-Level-∥-∥₁ : ∀ {n} → H-Level (suc n) ∥ A ∥₁
  H-Level-∥-∥₁ = hlevel-prop-instance squash₁

elim : {A : Type ℓ} {P : ∥ A ∥₁ → Type ℓ′}
     → Π[ x ꞉ ∥ A ∥₁ ] is-prop (P x)
     → Π[ x ꞉   A    ] P ∣ x ∣₁
     → Π[ x ꞉ ∥ A ∥₁ ] P   x
elim P-prop incc ∣ x ∣₁ = incc x
elim P-prop incc (squash₁ x y i) =
  is-prop→pathᴾ (λ j → P-prop (squash₁ x y j)) (elim P-prop incc x)
                                               (elim P-prop incc y)
                                               i

elim² : {P : ∥ A ∥₁ → ∥ B ∥₁ → Type ℓ″}
      → (∀ x y → is-prop (P x y))
      → (∀ x y → P ∣ x ∣₁ ∣ y ∣₁)
      → ∀ x y → P x y
elim² {A} {B} {P} P-prop work x y = go x y where
  go : ∀ x y → P x y
  go ∣ x ∣₁ ∣ y ∣₁ = work x y
  go ∣ x ∣₁ (squash₁ y y′ i) =
    is-prop→pathᴾ (λ i → P-prop ∣ x ∣₁ (squash₁ y y′ i))
                  (go ∣ x ∣₁ y) (go ∣ x ∣₁ y′) i

  go (squash₁ x y i) z =
    is-prop→pathᴾ (λ i → P-prop (squash₁ x y i) z)
                  (go x z) (go y z) i

rec : is-prop B → (A → B) → ∥ A ∥₁ → B
rec B-prop f ∣ x ∣₁ = f x
rec B-prop f (squash₁ x y i) = B-prop (rec B-prop f x) (rec B-prop f y) i

rec² : is-prop C
     → (A → B → C)
     → (x : ∥ A ∥₁) (y : ∥ B ∥₁) → C
rec² C-prop = elim² (λ _ _ → C-prop)

proj : (A-prop : is-prop A) → ∥ A ∥₁ → A
proj A-prop = rec A-prop id


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

elim!
  : {A : Type ℓ} {P : ∥ A ∥₁ → Type ℓ′}
    ⦃ P-prop : ∀{a} → H-Level 1 (P a) ⦄
  → Π[ a ꞉ A ] P ∣ a ∣₁
  → (x : ∥ A ∥₁) → P x
elim! = elim (λ _ → hlevel 1)

elim!² : {P : ∥ A ∥₁ → ∥ B ∥₁ → Type ℓ″}
       → ⦃ P-prop : ∀ {x y} → H-Level 1 (P x y) ⦄
       → (∀ x y → P ∣ x ∣₁ ∣ y ∣₁)
       → ∀ x y → P x y
elim!² = elim² (λ _ _ → hlevel 1)

rec!
  : ⦃ B-prop : H-Level 1 B ⦄
  → (A → B)
  → (x : ∥ A ∥₁) → B
rec! = elim!

rec!² : ⦃ C-prop : H-Level 1 C ⦄
      → (A → B → C)
      → (x : ∥ A ∥₁) (y : ∥ B ∥₁) → C
rec!² = elim!²

proj!
  : ⦃ A-prop : H-Level 1 A ⦄
  → ∥ A ∥₁ → A
proj! = rec! id
