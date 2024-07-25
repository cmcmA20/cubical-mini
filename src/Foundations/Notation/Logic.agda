{-# OPTIONS --safe #-}
module Foundations.Notation.Logic where

open import Foundations.Notation.Underlying
open import Foundations.Prim.Type

private variable
  ℓ ℓ′ ℓ″ : Level
  U : 𝒰 ℓ
  V : 𝒰 ℓ′
  W : 𝒰 ℓ″

-- TODO code duplication makes me sick, but using one generic notation
--      typeclass creates unpleasant goals after normalization

-- Quantifiers

record Π-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) ⦃ _ : Underlying A ⦄ (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : 𝒰ω where
  field Π : (X : A) (F : ⌞ X ⌟⁰ → B) → R

infixr 6 Π-syntax
Π-syntax
  : {A : Type ℓ} ⦃ u : Underlying A ⦄
    {B : Type ℓ′} {R : Type ℓ″}
    ⦃ p : Π-notation A B R ⦄
    (X : A) (F : ⌞ X ⌟⁰ → B)
  → R
Π-syntax ⦃ p ⦄ = p .Π-notation.Π
syntax Π-syntax X (λ x → F) = Π[ x ꞉ X ] F


record ∀-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) ⦃ _ : Underlying A ⦄ (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : 𝒰ω where
  field ∀′ : (X : A) (F : ⌞ X ⌟⁰ → B) → R

infixr 6 ∀-syntax
∀-syntax
  : {A : Type ℓ} ⦃ u : Underlying A ⦄
    {B : Type ℓ′} {R : Type ℓ″}
    ⦃ p : ∀-notation A B R ⦄
    (X : A) (F : ⌞ X ⌟⁰ → B)
  → R
∀-syntax ⦃ p ⦄ = p .∀-notation.∀′
syntax ∀-syntax X (λ x → F) = ∀[ x ꞉ X ] F


record Σ-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) ⦃ _ : Underlying A ⦄ (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : 𝒰ω where
  field Σ : (X : A) (F : ⌞ X ⌟⁰ → B) → R

infixr 6 Σ-syntax
Σ-syntax
  : {A : Type ℓ} ⦃ u : Underlying A ⦄
    {B : Type ℓ′} {R : Type ℓ″}
    ⦃ p : Σ-notation A B R ⦄
    (X : A) (F : ⌞ X ⌟⁰ → B)
  → R
Σ-syntax ⦃ p ⦄ = p .Σ-notation.Σ
syntax Σ-syntax X (λ x → F) = Σ[ x ꞉ X ] F


record ∃-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) ⦃ _ : Underlying A ⦄ (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : 𝒰ω where
  field ∃ : (X : A) (F : ⌞ X ⌟⁰ → B) → R

infixr 6 ∃-syntax
∃-syntax
  : {A : Type ℓ} ⦃ u : Underlying A ⦄
    {B : Type ℓ′} {R : Type ℓ″}
    ⦃ p : ∃-notation A B R ⦄
    (X : A) (F : ⌞ X ⌟⁰ → B)
  → R
∃-syntax ⦃ p ⦄ = p .∃-notation.∃
syntax ∃-syntax X (λ x → F) = ∃[ x ꞉ X ] F



-- Connectives

record ×-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 8 _×_
  field _×_ : A → B → R

open ×-notation ⦃ ... ⦄ public

record ⊎-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 7 _⊎_
  field _⊎_ : A → B → R

open ⊎-notation ⦃ ... ⦄ public

record ⊎₁-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 7 _⊎₁_
  field _⊎₁_ : A → B → R

open ⊎₁-notation ⦃ ... ⦄ public


record ⇒-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 6 _⇒_
  field _⇒_ : A → B → R

open ⇒-notation ⦃ ... ⦄ public


record ¬-notation {ℓᵃ ℓ}
  (A : 𝒰 ℓᵃ) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 0 ¬_
  field ¬_ : A → R

open ¬-notation ⦃ ... ⦄ public



-- Constants

record ⊥-notation {ℓ}
  (R : 𝒰 ℓ) : 𝒰ω where
  field ⊥ : R

open ⊥-notation ⦃ ... ⦄ public


record ⊤-notation {ℓ}
  (R : 𝒰 ℓ) : 𝒰ω where
  field ⊤ : R

open ⊤-notation ⦃ ... ⦄ public
