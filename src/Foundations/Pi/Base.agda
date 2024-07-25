{-# OPTIONS --safe #-}
module Foundations.Pi.Base where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Notation.Logic
open import Foundations.Notation.Reflexive
open import Foundations.Notation.Transitive
open import Foundations.Notation.Underlying
open import Foundations.Sigma.Base

private variable
  ℓ ℓ′ ℓ″ ℓᵃ ℓᵇ ℓᶜ : Level

instance
  Π-Type : {A : Type ℓ} ⦃ u : Underlying A ⦄
         → Π-notation A (Type ℓ′) (Type (u .ℓ-underlying ⊔ ℓ′))
  Π-Type .Π-notation.Π A B = (x : ⌞ A ⌟⁰) → B x

  ∀-Type : {A : Type ℓ} ⦃ u : Underlying A ⦄
         → ∀-notation A (Type ℓ′) (Type (u .ℓ-underlying ⊔ ℓ′))
  ∀-Type .∀-notation.∀′ A B = {x : ⌞ A ⌟⁰} → B x

infixr 6 Πᴱ-syntax
Πᴱ-syntax
  : {A : Type ℓ} ⦃ _ : Underlying A ⦄ (X : A) (F : @0 ⌞ X ⌟⁰ → Type ℓ′)
  → Type _
Πᴱ-syntax X F = (@0 x : ⌞ X ⌟⁰) → F x
syntax Πᴱ-syntax X (λ x → F) = Πᴱ[ x ꞉ X ] F

infixr 6 ∀ᴱ-syntax
∀ᴱ-syntax
  : {A : Type ℓ} ⦃ _ : Underlying A ⦄ (X : A) (F : @0 ⌞ X ⌟⁰ → Type ℓ′)
  → Type _
∀ᴱ-syntax X F = {@0 x : ⌞ X ⌟⁰} → F x
syntax ∀ᴱ-syntax X (λ x → F) = ∀ᴱ[ x ꞉ X ] F


-- non-dependent stuff

module _ where
  private variable
    A : Type ℓᵃ
    B : Type ℓᵇ
    C : Type ℓᶜ

  Fun : (A : Type ℓᵃ) (B : Type ℓᵇ) → Type (ℓᵃ ⊔ ℓᵇ)
  Fun A B = A → B

  flip : {C : A → B → Type ℓᶜ} → (∀ a b → C a b) → (∀ b a → C a b)
  flip f b a = f a b
  {-# INLINE flip #-}

  flipˢ : (A → B → C) → (B → A → C)
  flipˢ f b a = f a b
  {-# INLINE flipˢ #-}

  const : A → @0 B → A
  const x _ = x
  {-# INLINE const #-}

  id : A → A
  id x = x
  {-# INLINE id #-}

  infixr 9 _∘ₜˢ_
  _∘ₜˢ_ : (B → C) → (A → B) → (A → C)
  (g ∘ₜˢ f) x = g (f x)
  {-# INLINE _∘ₜˢ_ #-}

instance
  Refl-Fun : Refl (Fun {ℓ})
  Refl-Fun .refl = id

  Trans-Fun : Trans (Fun {ℓᵃ} {ℓᵇ}) (Fun {ℓᵇ = ℓᶜ}) Fun
  Trans-Fun ._∙_ f g = g ∘ₜˢ f


-- dependent stuff

module _ where

  private variable
    A : Type ℓᵃ
    B : A → Type ℓᵇ
    C : (a : A) → B a → Type ℓᶜ

  infixr -1 _$ₜ_
  _$ₜ_ : (f : (a : A) → B a) (x : A) → B x
  f $ₜ a = f a
  {-# INLINE _$ₜ_ #-}

  infixl -1 _&_
  _&_ : (x : A) (f : (a : A) → B a) → B x
  a & f = f a
  {-# INLINE _&_ #-}

  infixr 9 _∘_
  _∘_ : (g : {a : A} (b : B a) → C a b)
        (f : (a : A) → B a)
        (x : A)
      → C x (f x)
  (g ∘ f) x = g (f x)
  {-# INLINE _∘_ #-}

  infixr -1 _$ₛ_
  _$ₛ_ : {B : A → SSet ℓᵇ}
         (f : (a : A) → B a) (x : A) → B x
  f $ₛ x = f x
  {-# INLINE _$ₛ_ #-}

  case_return_of_ : (x : A) (B : A → Type ℓᵇ) (f : (a : A) → B a) → B x
  case x return P of f = f x
  {-# INLINE case_return_of_ #-}

  case_of_ : (x : A) (f : (a : A) → B a) → B x
  case x of f = f x
  {-# INLINE case_of_ #-}

  implicit : ((a : A) → B a) → ({x : A} → B x)
  implicit f {x} = f x

  explicit : ({a : A} → B a) → ((x : A) → B x)
  explicit f x = f {x}

is-contrᴱ : ∀ {ℓ} → Type ℓ → Type ℓ
is-contrᴱ A = Σ[ x ꞉ A ] Erased (Π[ y ꞉ A ] (x ＝ y))

is-equivᴱ : {A : Type ℓ} {B : Type ℓ′} (f : A → B) → Type _
is-equivᴱ {B} f = Π[ b ꞉ B ] is-contrᴱ (fibreᴱ f b)

instance
  ⇒-Type : ⇒-notation (𝒰 ℓ) (𝒰 ℓ′) _
  ⇒-Type ._⇒_ A B = A → B
