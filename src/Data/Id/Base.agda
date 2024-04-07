{-# OPTIONS --safe #-}
module Data.Id.Base where

open import Foundations.Base
  renaming ( _＝_ to _＝ₚ_
           ; refl to reflₚ
           ; sym  to symₚ
           ; _∙_  to _∙ₚ_
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

refl : x ＝ x
refl _ = id

sym : x ＝ y → y ＝ x
sym p _ q = q ∙ₚ symₚ (p _ reflₚ)

infixr 30 _∙_
_∙_ : x ＝ y → y ＝ z → x ＝ z
(p ∙ q) _ = q _ ∘ p _

transportˢ : A ＝ B → A → B
transportˢ p = transport (p _ reflₚ)

apˢ : (f : A → B) → x ＝ y → f x ＝ f y
apˢ f p _ q = q ∙ₚ ap f (p _ reflₚ)

substˢ : (P : A → Type ℓ)
       → x ＝ y → P x → P y
substˢ P = transportˢ ∘ apˢ P

_on-pathsˢ-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-pathsˢ-of A = Π[ a ꞉ A ] Π[ a′ ꞉ A ] S (a ＝ a′)

is-discreteˢ : Type ℓ → Type ℓ
is-discreteˢ = Dec on-pathsˢ-of_
