{-# OPTIONS --safe #-}
module Meta.Underlying where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Nat.Base

record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟⁰          : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ public

{-# DISPLAY Underlying.⌞_⌟⁰ f x = ⌞ x ⌟⁰ #-}

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : A → Type ℓ′
  P : Type ℓ′

instance
  Underlying-Σ : ⦃ ua : Underlying A ⦄ → Underlying (Σ A B)
  Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Σ .⌞_⌟⁰ x = ⌞ x .fst ⌟⁰

  Underlying-Type : Underlying (Type ℓ)
  Underlying-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟⁰ x = x

  Underlying-Lift : ⦃ ua : Underlying A ⦄ → Underlying (Lift ℓ′ A)
  Underlying-Lift ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Lift .⌞_⌟⁰ x = ⌞ x .lower ⌟⁰


infix 5 _∈_
_∈_ : ⦃ u : Underlying P ⦄ → A → (A → P) → Type _
x ∈ P = ⌞ P x ⌟⁰

infix 5 _∉_
_∉_ : ⦃ u : Underlying P ⦄ → A → (A → P) → Type _
x ∉ P = ¬ x ∈ P

_⊆_ : ⦃ u : Underlying P ⦄ → (A → P) → (A → P) → Type _
U ⊆ V = {x : _} → x ∈ U → x ∈ V


-- Notation class for type families which are "function-like" (always
-- nondependent)
record
  Funlike {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : Type ℓ′} (F : A → B → Type ℓ″) : Typeω where
  infixl 999 _#_

  field
    -- The domain and codomain of F must both support an underlying-type
    -- projection, which is determined by the F.
    overlap ⦃ au ⦄ : Underlying A
    overlap ⦃ bu ⦄ : Underlying B

    -- The underlying function (infix).
    _#_ : ∀ {A B} → F A B → ⌞ A ⌟⁰ → ⌞ B ⌟⁰

open Funlike ⦃ ... ⦄ using (_#_) public
{-# DISPLAY Funlike._#_ p f x = f # x #-}

-- Sections of the _#_ operator tend to be badly-behaved since they
-- introduce an argument x : ⌞ ?0 ⌟ whose Underlying instance meta
-- "mutually blocks" the Funlike instance meta. Use the prefix version
-- instead.
apply
  : {A : Type ℓ} {B : Type ℓ′ } {F : A → B → Type ℓ″}
  → ⦃ _ : Funlike F ⦄
  → ∀ {a b} → F a b → ⌞ a ⌟⁰ → ⌞ b ⌟⁰
apply = _#_

-- Generalised happly.
_#ₚ_
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {F : A → B → Type ℓ''}
  → ⦃ _ : Funlike F ⦄
  → {a : A} {b : B} {f g : F a b} → f ＝ g → ∀ (x : ⌞ a ⌟⁰) → f # x ＝ g # x
f #ₚ x = ap² _#_ f refl

instance
  Funlike-Fun : Funlike {A = Type ℓ} {B = Type ℓ′} (λ x y → x → y)
  Funlike-Fun = record { _#_ = _$_ }

  Funlike-≃ : Funlike {A = Type ℓ} {B = Type ℓ′} _≃_
  Funlike-≃ = record { _#_ = fst }

  Funlike-Iso : Funlike {A = Type ℓ} {B = Type ℓ′} Iso
  Funlike-Iso = record { _#_ = fst }
