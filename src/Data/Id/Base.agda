{-# OPTIONS --safe #-}
module Data.Id.Base where

open import Foundations.Base
  renaming ( _＝_ to _＝ₚ_
           ; apˢ  to apₚˢ
           )

open import Data.Dec.Base

-- Martin Escardo's equality
_＝_ : ∀{ℓ} {A : 𝒰 ℓ} (x y : A) → 𝒰 ℓ
x ＝ y = (z : _) → z ＝ₚ x → z ＝ₚ y

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  x y z : A

instance
  Refl-＝ : Refl (_＝_ {A = A})
  Refl-＝ .refl _ = id

  Sym-＝ : Sym (_＝_ {A = A})
  Sym-＝ ._ᵒᵖ p _ q = q ∙ p _ refl ⁻¹

  Trans-＝ : Trans (_＝_ {A = A})
  Trans-＝ ._∙_ p q _ = q _ ∘ p _

transportˢ : A ＝ B → A → B
transportˢ p = transport (p _ refl)

apˢ : (f : A → B) → x ＝ y → f x ＝ f y
apˢ f p _ q = q ∙ ap f (p _ refl)

substˢ : (P : A → Type ℓ)
       → x ＝ y → P x → P y
substˢ P = transportˢ ∘ apˢ P

_on-pathsˢ-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-pathsˢ-of A = Π[ a ꞉ A ] Π[ a′ ꞉ A ] S (a ＝ a′)

is-discreteˢ : Type ℓ → Type ℓ
is-discreteˢ = Dec on-pathsˢ-of_
