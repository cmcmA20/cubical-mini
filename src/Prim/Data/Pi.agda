{-# OPTIONS --safe #-}
module Prim.Data.Pi where

open import Prim.Type

private variable ℓ ℓ′ ℓ″ : Level

infix 6 Π-syntax
Π-syntax : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
Π-syntax A B = (x : A) → B x

syntax Π-syntax A (λ x → B) = Π[ x ꞉ A ] B

flip : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
     → (A → B → C) → (B → A → C)
flip f b a = f a b
{-# INLINE flip #-}

const : {A : Type ℓ} {B : Type ℓ′}
      → A → B → A
const x = λ _ → x
{-# INLINE const #-}

id : {A : Type ℓ} → A → A
id x = x
{-# INLINE id #-}

infixr -1 _$_
_$_ : {A : Type ℓ} {B : A → Type ℓ′}
    → ((a : A) → B a) → (a : A) → B a
f $ a = f a
{-# INLINE _$_ #-}

infixr 9 _∘_ _∘′_
_∘_ : {A : Type ℓ} {B : A → Type ℓ′} {C : (a : A) → B a → Type ℓ″}
      (g : {a : A} → (b : B a) → C a b)
    → (f : (a : A) → B a)
    → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)
{-# INLINE _∘_ #-}

_∘′_ : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
     → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)
{-# INLINE _∘′_ #-}

infixr -1 _$ₛ_
_$ₛ_ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → SSet ℓ′} → ((x : A) → B x) → ((x : A) → B x)
f $ₛ x = f x
{-# INLINE _$ₛ_ #-}
