{-# OPTIONS --safe #-}
module Prim.Data.Pi where

open import Prim.Type

private variable
  ℓ ℓ′ ℓ″ : Level

infix 6 Π-syntax
Π-syntax : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
Π-syntax A B = (x : A) → B x

syntax Π-syntax A (λ x → B) = Π[ x ꞉ A ] B


-- non-dependent stuff

module _ where
  private variable
    A : Type ℓ
    B : Type ℓ′
    C : Type ℓ″

  flip : (A → B → C) → (B → A → C)
  flip f b a = f a b
  {-# INLINE flip #-}

  const : A → B → A
  const x _ = x
  {-# INLINE const #-}

  id : A → A
  id x = x
  {-# INLINE id #-}

  infixr 9 _∘′_
  _∘′_ : (B → C) → (A → B) → (A → C)
  (g ∘′ f) x = g (f x)
  {-# INLINE _∘′_ #-}


-- dependent stuff

module _ where

  private variable
    A : Type ℓ
    B : A → Type ℓ′
    C : (a : A) → B a → Type ℓ″

  infixr -1 _$_
  _$_ : (f : (a : A) → B a) (x : A) → B x
  f $ a = f a
  {-# INLINE _$_ #-}

  infixr 9 _∘_
  _∘_ : (g : {a : A} (b : B a) → C a b)
        (f : (a : A) → B a)
        (x : A)
      → C x (f x)
  (g ∘ f) x = g (f x)
  {-# INLINE _∘_ #-}

  infixr -1 _$ₛ_
  _$ₛ_ : {B : A → SSet ℓ′}
         (f : (a : A) → B a) (x : A) → B x
  f $ₛ x = f x
  {-# INLINE _$ₛ_ #-}

  case_return_of_ : (x : A) (B : A → Type ℓ′) (f : (a : A) → B a) → B x
  case x return P of f = f x
  {-# INLINE case_return_of_ #-}

  case_of_ : (x : A) (f : (a : A) → B a) → B x
  case x of f = f x
  {-# INLINE case_of_ #-}
