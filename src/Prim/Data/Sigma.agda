{-# OPTIONS --safe #-}
module Prim.Data.Sigma where

open import Prim.Type

open import Agda.Builtin.Sigma public

infix 2 Σ-syntax
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ꞉ A ] B

private variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ ℓᶠ : Level
  A : Type ℓ
  B : A → Type ℓ′
  C : (a : A) → B a → Type ℓ″
  D : (a : A) (b : B a) → C a b → Type ℓ‴
  E : (a : A) (b : B a) (c : C a b) → D a b c → Type ℓ⁗
  F : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d → Type ℓᶠ

infixr 4 _×_
_×_ : (A : Type ℓ) (B : Type ℓ′) → Type (level-of-type A ⊔ level-of-type B)
A × B = Σ[ _ ꞉ A ] B

∃ᶜ : (B : A → Type ℓ′) → Type (level-of-type A ⊔ ℓ′)
∃ᶜ = Σ _

∃₂ᶜ : {B : A → Type ℓ′} (C : (x : A) → B x → Type ℓ″) → Type (level-of-type A ⊔ ℓ′ ⊔ ℓ″)
∃₂ᶜ C = ∃ᶜ λ a → ∃ᶜ λ b → C a b

infix 2 ∃ᶜ-syntax
∃ᶜ-syntax : (A → Type ℓ′) → Type (level-of-type A ⊔ ℓ′)
∃ᶜ-syntax = ∃ᶜ

syntax ∃ᶜ-syntax (λ x → B) = ∃ᶜ[ x ] B

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

curry₂ : (f : (p : Σ[ a ꞉ A ] B a) → C (fst p) (snd p))
         (x : A) (y : B x) → C x y
curry₂ f x y = f (x , y)
