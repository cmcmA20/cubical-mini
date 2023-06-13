{-# OPTIONS --safe #-}
module Data.Id where

open import Foundations.Base
open import Foundations.Transport
open import Foundations.HLevel.Base
open import Foundations.Equiv

open import Meta.Reflection.HLevel

open import Structures.Base
open import Structures.IdentitySystem

open import Correspondences.Nullary.Discrete

open import Data.Dec.Base

open import Agda.Builtin.Equality public
  using ()
  renaming ( _≡_  to _＝ⁱ_
           ; refl to reflⁱ )

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  x y z : A
  B : Type ℓ′
  f : A → B
  n : HLevel
  S : Type ℓ → Type ℓ′

Id-identity-system : is-identity-system (_＝ⁱ_ {A = A}) (λ _ → reflⁱ)
Id-identity-system .to-path      reflⁱ = refl
Id-identity-system .to-path-over reflⁱ = refl

apⁱ : (f : A → B) → x ＝ⁱ y → f x ＝ⁱ f y
apⁱ f reflⁱ = reflⁱ

symⁱ : x ＝ⁱ y → y ＝ⁱ x
symⁱ reflⁱ = reflⁱ

_∙ⁱ_ : x ＝ⁱ y → y ＝ⁱ z → x ＝ⁱ z
reflⁱ ∙ⁱ q = q

substⁱ : (P : A → Type ℓ′)
       → x ＝ⁱ y → P x → P y
substⁱ P reflⁱ x = x

_ : substⁱ (λ x → x) reflⁱ x ＝ x
_ = refl


Id≃path : (x ＝ⁱ y) ≃ (x ＝ y)
Id≃path = identity-system-gives-path Id-identity-system

module Id≃path {ℓ} {A : Type ℓ} = Ids (Id-identity-system {A = A})


is-of-hlevelⁱ : HLevel → Type ℓ → Type ℓ
is-of-hlevelⁱ 0 A = Σ[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ⁱ y)
is-of-hlevelⁱ (suc 0) A = Π[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ⁱ y)
is-of-hlevelⁱ (suc (suc h)) A = Π[ x ꞉ A ] Π[ y ꞉ A ] is-of-hlevelⁱ (suc h) (x ＝ⁱ y)

is-contrⁱ : Type ℓ → Type ℓ
is-contrⁱ = is-of-hlevelⁱ 0

is-propⁱ : Type ℓ → Type ℓ
is-propⁱ = is-of-hlevelⁱ 1

is-setⁱ : Type ℓ → Type ℓ
is-setⁱ = is-of-hlevelⁱ 2

is-contrⁱ→is-contr : is-contrⁱ A → is-contr A
is-contrⁱ→is-contr (centre , _) .fst = centre
is-contrⁱ→is-contr (_ , paths)  .snd x = Id≃path.to (paths x)

is-propⁱ→is-prop : is-propⁱ A → is-prop A
is-propⁱ→is-prop A-propⁱ x y = Id≃path.to (A-propⁱ x y)

is-setⁱ→is-set : is-setⁱ A → is-set A
is-setⁱ→is-set A-setⁱ x y p q =
  let z = A-setⁱ x y (Id≃path.from p) (Id≃path.from q)
      w = apⁱ Id≃path.to z
  in Id≃path.to (subst₂ _＝ⁱ_ (Id≃path.ε _) (Id≃path.ε _) w)


_on-pathsⁱ-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-pathsⁱ-of A = Π[ a ꞉ A ] Π[ a′ ꞉ A ] S (a ＝ⁱ a′)

is-discreteⁱ : Type ℓ → Type ℓ
is-discreteⁱ A = Dec on-pathsⁱ-of A

is-discreteⁱ→is-discrete : is-discreteⁱ A → is-discrete A
is-discreteⁱ→is-discrete d x y =
  map (Id≃path .fst)
      (λ ¬pⁱ p → ¬pⁱ ((Id≃path ₑ⁻¹) .fst p))
      (d x y)
