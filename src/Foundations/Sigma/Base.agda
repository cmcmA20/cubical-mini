{-# OPTIONS --safe #-}
module Foundations.Sigma.Base where

open import Foundations.Prim.Type

open import Agda.Builtin.Sigma public

private variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ ℓᶠ : Level
  A : Type ℓ
  B : A → Type ℓ′
  C : (a : A) → B a → Type ℓ″
  D : (a : A) (b : B a) → C a b → Type ℓ‴
  E : (a : A) (b : B a) (c : C a b) → D a b c → Type ℓ⁗
  F : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d → Type ℓᶠ

infix 2 Σ-syntax
Σ-syntax : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
Σ-syntax = Σ
{-# INLINE Σ-syntax #-}
syntax Σ-syntax A (λ x → B) = Σ[ x ꞉ A ] B

infixr 4 _×_
_×_ : (A : Type ℓ) (B : Type ℓ′) → Type (level-of-type A ⊔ level-of-type B)
A × B = Σ[ _ ꞉ A ] B

infix 2 Σ-syntax′
Σ-syntax′ : (B : A → Type ℓ′) → Type _
Σ-syntax′ {A} = Σ A
{-# INLINE Σ-syntax′ #-}
syntax Σ-syntax′ (λ x → B) = Σ[ x ] B

<_,_> : {C : ∀ {a} → B a → Type ℓ″}
      → (f : (x : A) → B x)
      → ((x : A) → C (f x))
      → ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

bimap : {P : A → Type ℓ″} {Q : ∀ {a} → P a → B a → Type ℓ‴}
      → (f : (a : A) → B a)
      → (∀ {a} (b : P a) → Q b (f a))
      → ((a , b) : Σ A P)
      → Σ (B a) (Q b)
bimap f g (x , y) = f x , g y

bimap-simple : {B : Type ℓ′} {P : A → Type ℓ″} {Q : B → Type ℓ‴}
             → (f : A → B)
             → (∀ {x} → P x → Q (f x))
             → Σ A P → Σ B Q
bimap-simple = bimap

first : {B : Type ℓ′} {C : Type ℓ″} → (A → B) → A × C → B × C
first f = bimap f (λ x → x)

second : {C : A → Type ℓ‴} → (∀ {x} → B x → C x) → Σ A B → Σ A C
second f = bimap (λ x → x) f


_$₂_ : (f : (a : A) (b : B a) → C a b)
       (p : Σ[ x ꞉ A ] B x)
     → C (fst p) (snd p)
f $₂ (x , y) = f x y

-- TODO: automate this to get `curryₙ` and `uncurryₙ` (`_$ₙ_`)
_$₃_ : (f : (a : A) (b : B a) (c : C a b) → D a b c)
       (p : Σ[ x ꞉ A ] Σ[ y ꞉ B x ] C x y)
     → D (p .fst) (p .snd .fst) (p .snd .snd)
f $₃ (x , y , z) = f x y z

_$₄_ : (f : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d)
       (p : Σ[ x ꞉ A ] Σ[ y ꞉ B x ] Σ[ z ꞉ C x y ] D x y z)
     → E (p .fst) (p .snd .fst) (p .snd .snd .fst) (p .snd .snd .snd)
f $₄ (x , y , z , w) = f x y z w

_$₅_ : (f : (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) → F a b c d e)
       (p : Σ[ x ꞉ A ] Σ[ y ꞉ B x ] Σ[ z ꞉ C x y ] Σ[ w ꞉ D x y z ] E x y z w)
     → F (p .fst) (p .snd .fst) (p .snd .snd .fst) (p .snd .snd .snd .fst) (p .snd .snd .snd .snd)
f $₅ (x , y , z , w , u) = f x y z w u

-- note that `curry₁` is just `_$_`

curry₂ : (f : (p : Σ[ a ꞉ A ] B a) → C (p .fst) (p .snd))
         (x : A) (y : B x) → C x y
curry₂ f x y = f (x , y)

curry₃ : (f : (p : Σ[ a ꞉ A ] Σ[ b ꞉ B a ] C a b) → D (p .fst) (p .snd .fst) (p .snd .snd))
         (x : A) (y : B x) (z : C x y) → D x y z
curry₃ f x y z = f (x , y , z)

uncurry : {B : 𝒰 ℓ} {C : 𝒰 ℓ′} (f : A → B → C) → A × B → C
uncurry f (a , b) = f a b
