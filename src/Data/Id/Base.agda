{-# OPTIONS --safe #-}
module Data.Id.Base where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel

open import Data.Dec.Base

open import Agda.Builtin.Equality public
  using ()
  renaming ( _≡_  to _＝ⁱ_
           ; refl to reflⁱ )

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  x y z : A

apⁱ : (f : A → B) → x ＝ⁱ y → f x ＝ⁱ f y
apⁱ f reflⁱ = reflⁱ

symⁱ : x ＝ⁱ y → y ＝ⁱ x
symⁱ reflⁱ = reflⁱ

_∙ⁱ_ : x ＝ⁱ y → y ＝ⁱ z → x ＝ⁱ z
reflⁱ ∙ⁱ reflⁱ = reflⁱ

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
