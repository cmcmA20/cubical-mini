{-# OPTIONS --safe #-}
module Data.Id.Inductive.Base where

open import Foundations.Base
open import Foundations.HLevel

open import Data.Dec.Base

open import Agda.Builtin.Equality public
  using ()
  renaming ( _≡_  to _＝ⁱ_
           ; refl to reflⁱ )

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  D : Type ℓᵈ
  x y z : A

apⁱ : (f : A → B) → x ＝ⁱ y → f x ＝ⁱ f y
apⁱ f reflⁱ = reflⁱ

apⁱ²
  : (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B}
  → x₁ ＝ⁱ x₂ → y₁ ＝ⁱ y₂
  → f x₁ y₁ ＝ⁱ f x₂ y₂
apⁱ² f reflⁱ reflⁱ = reflⁱ

apⁱ³
  : (f : A → B → C → D) {x₁ x₂ : A} {y₁ y₂ : B} {z₁ z₂ : C}
  → x₁ ＝ⁱ x₂ → y₁ ＝ⁱ y₂ → z₁ ＝ⁱ z₂
  → f x₁ y₁ z₁ ＝ⁱ f x₂ y₂ z₂
apⁱ³ f reflⁱ reflⁱ reflⁱ = reflⁱ

instance
  Refl-＝ⁱ : Reflexive (_＝ⁱ_ {A = A})
  Refl-＝ⁱ .refl = reflⁱ

  Symm-＝ⁱ : Symmetric (_＝ⁱ_ {A = A})
  Symm-＝ⁱ ._⁻¹ reflⁱ = reflⁱ

  Trans-＝ⁱ : Transitive (_＝ⁱ_ {A = A})
  Trans-＝ⁱ ._∙_ reflⁱ reflⁱ = reflⁱ

transportⁱ : A ＝ⁱ B → A → B
transportⁱ reflⁱ = id

substⁱ : (P : A → Type ℓ)
       → x ＝ⁱ y → P x → P y
substⁱ P = transportⁱ ∘ apⁱ P


is-of-hlevelⁱ : HLevel → Type ℓ → Type ℓ
is-of-hlevelⁱ 0 A = Σ[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ⁱ y)
is-of-hlevelⁱ 1 A = Π[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ⁱ y)
is-of-hlevelⁱ (suc (suc h)) A = Π[ x ꞉ A ] Π[ y ꞉ A ] is-of-hlevelⁱ (suc h) (x ＝ⁱ y)

is-contrⁱ : Type ℓ → Type ℓ
is-contrⁱ = is-of-hlevelⁱ 0

is-propⁱ : Type ℓ → Type ℓ
is-propⁱ = is-of-hlevelⁱ 1

is-setⁱ : Type ℓ → Type ℓ
is-setⁱ = is-of-hlevelⁱ 2

_on-pathsⁱ-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-pathsⁱ-of A = Π[ a ꞉ A ] Π[ a′ ꞉ A ] S (a ＝ⁱ a′)

is-discreteⁱ : Type ℓ → Type ℓ
is-discreteⁱ = Dec on-pathsⁱ-of_
