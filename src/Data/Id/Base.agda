{-# OPTIONS --safe #-}
module Data.Id.Base where

open import Foundations.Base

open import Data.Dec.Base

-- Martin Escardo's equality
_＝ˢ_ : ∀{ℓ} {A : 𝒰 ℓ} (x y : A) → 𝒰 ℓ
x ＝ˢ y = (z : _) → z ＝ x → z ＝ y

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  x y z : A

reflˢ : x ＝ˢ x
reflˢ _ = id

symˢ : x ＝ˢ y → y ＝ˢ x
symˢ p _ q = q ∙ sym (p _ refl)

infixr 30 _∙ˢ_
_∙ˢ_ : x ＝ˢ y → y ＝ˢ z → x ＝ˢ z
(p ∙ˢ q) _ = q _ ∘ p _

transportˢ : A ＝ˢ B → A → B
transportˢ p = transport (p _ refl)

apˢ : (f : A → B) → x ＝ˢ y → f x ＝ˢ f y
apˢ f p _ q = q ∙ ap f (p _ refl)

substˢ : (P : A → Type ℓ)
       → x ＝ˢ y → P x → P y
substˢ P = transportˢ ∘ apˢ P

_on-pathsˢ-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-pathsˢ-of A = Π[ a ꞉ A ] Π[ a′ ꞉ A ] S (a ＝ˢ a′)

is-discreteˢ : Type ℓ → Type ℓ
is-discreteˢ = Dec on-pathsˢ-of_
