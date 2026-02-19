{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Base where

open import Meta.Prelude

open import Data.Bool.Base using (Bool)
open import Data.Empty.Base using ()
open import Data.Reflects.Base as Reflects
open import Data.Sum.Base using ()

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

rec : {A : Type ℓ} {B : Type ℓ′}
    → is-prop B
    → (A → B)
    → ∥ A ∥₁ → B
rec pb = elim (λ _ → pb)

-- Mere existence

-- ∃ : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
-- ∃ A B = ∥ Σ[ B ] ∥₁

instance
  ∃-Type
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → ∃-notation A (Type ℓ′) (Type (ua .ℓ-underlying ⊔ ℓ′))
  ∃-Type .∃-notation.∃ X F = ∥ Σ[ F ] ∥₁

Existential₁ⁿ : Variadic-binding¹
Existential₁ⁿ = ∥_∥₁ ∘ Existentialⁿ

infixr 6 ∃[_]
∃[_] : ⦃ r : Total-Σ A ⦄ → A → Type (r .ℓ-total-Σ)
∃[_] f = ∥ Σ[ f ] ∥₁


-- Mere disjunction
instance
  ⊎₁-Type : ⊎₁-notation (Type ℓ) (Type ℓ′) (Type (ℓ ⊔ ℓ′))
  ⊎₁-Type .⊎₁-notation.Constraint _ _ = ⊤ₜ
  ⊎₁-Type ._⊎₁_ A B = ∥ A ⊎ B ∥₁

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

  Reflects-∥-∥₁ : {b : Bool} → ⦃ Reflects A b ⦄ → Reflects ∥ A ∥₁ b
  Reflects-∥-∥₁ = Reflects.dmap ∣_∣₁ rec! auto

proj!
  : ⦃ A-prop : H-Level 1 A ⦄
  → ∥ A ∥₁ → A
proj! = rec! id
