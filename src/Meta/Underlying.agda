{-# OPTIONS --safe #-}
module Meta.Underlying where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Bool.Base
open import Data.Empty.Base
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


-- Notation class for type families which are "function-like"
-- Looks like it's dependent now
record
  Funlike {ℓ ℓ′ ℓ″} (A : Type ℓ) (Arg : Type ℓ′) (F : Arg → Type ℓ″) : Type (ℓ ⊔ ℓ′ ⊔ ℓ″) where
  infixl 999 _#_
  field _#_ : A → (x : Arg) → F x

open Funlike ⦃ ... ⦄ using (_#_) public
{-# DISPLAY Funlike._#_ p f x = f # x #-}

-- Sections of the _#_ operator tend to be badly-behaved since they
-- introduce an argument x : ⌞ ?0 ⌟ whose Underlying instance meta
-- "mutually blocks" the Funlike instance meta. Use the prefix version
-- instead.
apply
  : {A : Type ℓ} {B : A → Type ℓ′} {F : Type ℓ″}
  → ⦃ _ : Funlike F A B ⦄
  → F → (x : A) → B x
apply = _#_

ap#
  : {A : Type ℓ} {B : A → Type ℓ′} {F : Type ℓ″}
  → ⦃ _ : Funlike F A B ⦄
  → (f : F) {x y : A} (p : x ＝ y)
  → ＜ f # x ／ (λ i → B (p i)) ＼ f # y ＞
ap# f = ap (apply f)

-- Generalised happly.
_#ₚ_
  : {A : Type ℓ} {B : A → Type ℓ′} {F : Type ℓ″}
  → ⦃ _ : Funlike F A B ⦄
  → {f g : F} → f ＝ g → (x : A) → f # x ＝ g # x
f #ₚ x = ap² _#_ f refl

instance
  Funlike-≃ : {A : Type ℓ} {B : Type ℓ′} → Funlike (A ≃ B) A (λ _ → B)
  Funlike-≃ ._#_ = fst

  Funlike-Iso : {A : Type ℓ} {B : Type ℓ′} → Funlike (Iso A B) A (λ _ → B)
  Funlike-Iso ._#_ = fst

  Funlike-Π : {A : Type ℓ} {B : A → Type ℓ′} → Funlike (Π[ a ꞉ A ] B a) A B
  Funlike-Π ._#_ = id

  Funlike-Homotopy
    : {A : Type ℓ} {B : A → Type ℓ′} {f g : ∀ x → B x}
    → Funlike (f ＝ g) A (λ x → f x ＝ g x)
  Funlike-Homotopy ._#_ = happly


-- Generalised "sections" (e.g. of a presheaf) notation.
infix 999 _ʻ_
_ʻ_
  : {A : Type ℓ} {B : A → Type ℓ′} {F : Type ℓ″}
  → ⦃ _ : Funlike F A B ⦄
  → F → (x : A) → ⦃ _ : Underlying (B x) ⦄
  → Type _
F ʻ x = ⌞ F # x ⌟⁰
