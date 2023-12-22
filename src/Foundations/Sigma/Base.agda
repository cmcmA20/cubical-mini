{-# OPTIONS --safe #-}
module Foundations.Sigma.Base where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Agda.Builtin.Sigma public

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ ℓᵈ ℓᵉ ℓᶠ : Level
  A : Type ℓᵃ
  B : A → Type ℓᵇ
  C : (a : A) → B a → Type ℓᶜ
  D : (a : A) (b : B a) → C a b → Type ℓᵈ
  E : (a : A) (b : B a) (c : C a b) → D a b c → Type ℓᵉ
  F : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d → Type ℓᶠ

infixr 6 Σ-syntax
Σ-syntax : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
Σ-syntax = Σ
{-# INLINE Σ-syntax #-}
syntax Σ-syntax A (λ x → B) = Σ[ x ꞉ A ] B

infixr 8 _×_
_×_ : (A : Type ℓ) (B : Type ℓ′) → Type (level-of-type A ⊔ level-of-type B)
A × B = Σ[ _ ꞉ A ] B

<_,_> : {C : ∀ {a} → B a → Type ℓᶜ}
      → (f : (x : A) → B x)
      → ((x : A) → C (f x))
      → ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

bimap : {P : A → Type ℓ} {Q : ∀ {a} → P a → B a → Type ℓ′}
      → (f : (a : A) → B a)
      → (∀ {a} (b : P a) → Q b (f a))
      → ((a , b) : Σ A P)
      → Σ (B a) (Q b)
bimap f g (x , y) = f x , g y

bimap-simple : {B : Type ℓᵇ} {P : A → Type ℓ} {Q : B → Type ℓ′}
             → (f : A → B)
             → (∀ {x} → P x → Q (f x))
             → Σ A P → Σ B Q
bimap-simple = bimap

first : {C : A → Type ℓᶜ} → (f : (a : A) → B a) → ((a , _) : Σ A C) → B a × C a
first f = bimap f (λ x → x)

second : {C : A → Type ℓᶜ} → (∀ {x} → B x → C x) → Σ A B → Σ A C
second f = bimap (λ x → x) f


_$²_ : (f : (a : A) (b : B a) → C a b)
       (p : Σ[ x ꞉ A ] B x)
     → C (fst p) (snd p)
f $² (x , y) = f x y

-- TODO: automate this to get `curryⁿ` and `uncurryⁿ` (`_$ⁿ_`)
_$³_ : (f : (a : A) (b : B a) (c : C a b) → D a b c)
       (p : Σ[ x ꞉ A ] Σ[ y ꞉ B x ] C x y)
     → D (p .fst) (p .snd .fst) (p .snd .snd)
f $³ (x , y , z) = f x y z

_$⁴_ : (f : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d)
       (p : Σ[ x ꞉ A ] Σ[ y ꞉ B x ] Σ[ z ꞉ C x y ] D x y z)
     → E (p .fst) (p .snd .fst) (p .snd .snd .fst) (p .snd .snd .snd)
f $⁴ (x , y , z , w) = f x y z w

_$⁵_ : (f : (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) → F a b c d e)
       (p : Σ[ x ꞉ A ] Σ[ y ꞉ B x ] Σ[ z ꞉ C x y ] Σ[ w ꞉ D x y z ] E x y z w)
     → F (p .fst) (p .snd .fst) (p .snd .snd .fst) (p .snd .snd .snd .fst) (p .snd .snd .snd .snd)
f $⁵ (x , y , z , w , u) = f x y z w u

-- note that `curry¹` is just `_$_` again

curry² : (f : (p : Σ[ a ꞉ A ] B a) → C (p .fst) (p .snd))
         (x : A) (y : B x) → C x y
curry² f x y = f (x , y)

curry³ : (f : (p : Σ[ a ꞉ A ] Σ[ b ꞉ B a ] C a b) → D (p .fst) (p .snd .fst) (p .snd .snd))
         (x : A) (y : B x) (z : C x y) → D x y z
curry³ f x y z = f (x , y , z)


fibreᴱ : {A  : Type ℓᵃ} {@0 B : Type ℓᵇ} (f : A → B) (@0 y : B) → Type _
fibreᴱ {A} f y = Σ[ x ꞉ A ] Erased (f x ＝ y)
