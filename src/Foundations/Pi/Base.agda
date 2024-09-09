{-# OPTIONS --safe #-}
module Foundations.Pi.Base where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Notation.Associativity
open import Foundations.Notation.Closure
open import Foundations.Notation.Composition
open import Foundations.Notation.Logic
open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Underlying
open import Foundations.Notation.Unital.Inner
open import Foundations.Notation.Unital.Outer
open import Foundations.Sigma.Base

private variable ℓ ℓ′ ℓ″ ℓ‴ ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level

instance
  Π-Type
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → Π-notation A (Type ℓ′) (Type (ua .ℓ-underlying ⊔ ℓ′))
  Π-Type .Π-notation.Π A B = (x : ⌞ A ⌟) → B x

  Πᴱ-Type
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → Πᴱ-notation A (Type ℓ′) (Type (ua .ℓ-underlying ⊔ ℓ′))
  Πᴱ-Type .Πᴱ-notation.Πᴱ A B = (@0 x : ⌞ A ⌟) → B x

  ∀-Type
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → ∀-notation A (Type ℓ′) (Type (ua .ℓ-underlying ⊔ ℓ′))
  ∀-Type .∀-notation.∀′ A B = {x : ⌞ A ⌟} → B x

  ∀ᴱ-Type
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → ∀ᴱ-notation A (Type ℓ′) (Type (ua .ℓ-underlying ⊔ ℓ′))
  ∀ᴱ-Type .∀ᴱ-notation.∀ᴱ′ A B = {@0 x : ⌞ A ⌟} → B x

  Closure-Π-Variadic
    : {A : Type ℓ} {X : Type ℓ′}
      ⦃ tp : Closure-Π A ⦄
    → Closure-Π (X → A)
  Closure-Π-Variadic {ℓ′} ⦃ tp ⦄ .ℓ-total-Π = ℓ′ ⊔ tp .ℓ-total-Π
  Closure-Π-Variadic {X} .Π[_] f = (x : X) → Π[ f x ]
  {-# OVERLAPPING Closure-Π-Variadic #-}

  Closure-∀-Variadic
    : {A : Type ℓ} {X : Type ℓ′}
      ⦃ tp : Closure-∀ A ⦄
    → Closure-∀ (X → A)
  Closure-∀-Variadic {ℓ′} ⦃ tp ⦄ .ℓ-total-∀ = ℓ′ ⊔ tp .ℓ-total-∀
  Closure-∀-Variadic {X} .∀[_] f = {x : X} → ∀[ f x ]
  {-# OVERLAPPING Closure-∀-Variadic #-}

  Closure-∀ᴱ-Variadic
    : {A : Type ℓ} {X : Type ℓ′}
      ⦃ tp : Closure-∀ᴱ A ⦄
    → Closure-∀ᴱ (X → A)
  Closure-∀ᴱ-Variadic {ℓ′} ⦃ tp ⦄ .ℓ-total-∀ᴱ = ℓ′ ⊔ tp .ℓ-total-∀ᴱ
  Closure-∀ᴱ-Variadic {X} .∀ᴱ[_] f = {@0 x : X} → ∀ᴱ[ f x ]
  {-# OVERLAPPING Closure-∀ᴱ-Variadic #-}


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

  Comp-Fun : Comp (Fun {ℓᵃ} {ℓᵇ}) (Fun {ℓᵇ = ℓᶜ}) Fun
  Comp-Fun ._∙_ f g x = g (f x)

  GAssoc-Fun : GAssoc (Fun {ℓᵃ} {ℓᵇ}) (Fun {ℓᵇ = ℓᶜ}) (Fun {ℓᵇ = ℓᵈ}) Fun Fun Fun
  GAssoc-Fun .∙-assoc f g h _ a = h (g (f a))

  GUnit-i-Fun : GUnit-i (Fun {ℓᵃ} {ℓᵇ}) Fun
  GUnit-i-Fun .∙-id-i f _ a = f a

  GUnit-o-Fun : GUnit-o Fun (Fun {ℓᵃ} {ℓᵇ})
  GUnit-o-Fun .∙-id-o f _ a = f a


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
  ⇒-Type : ⇒-notation (Type ℓ) (Type ℓ′) (Type (ℓ ⊔ ℓ′))
  ⇒-Type ._⇒_ A B = A → B
