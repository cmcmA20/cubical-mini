{-# OPTIONS --safe #-}
module Prim.Kan where

open import Prim.Type
open import Prim.Interval
open import Prim.Extension

open import Agda.Primitive.Cubical
  using ( primHComp
        ; primComp )

open import Agda.Primitive.Cubical public
  using ()
  renaming ( primTransp to transp )

private variable
  ℓ ℓ′ : Level
  ℓ^ : I → Level

hcomp : {A : Type ℓ} (φ : I)
      → (u : (i : I) → Partial (φ ∨ ~ i) A)
      → A
hcomp φ u = primHComp (λ j .o → u j (leftIs1 φ (~ j) o)) (u i0 1=1)

∂ : I → I
∂ i = i ∨ ~ i

comp : (A : (i : I) → Type (ℓ^ i)) (φ : I)
     → (u : (i : I) → Partial (φ ∨ ~ i) (A i))
     → A i1
comp A φ u = primComp A (λ j .o → u j (leftIs1 φ (~ j) o)) (u i0 1=1)

hfill : {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
hfill φ i u =
  hcomp (φ ∨ ~ i) λ where
    j (φ = i1) → u (i ∧ j) 1=1
    j (i = i0) → u i0      1=1
    j (j = i0) → u i0      1=1

fill : (A : ∀ i → Type (ℓ^ i)) (φ : I) (i : I)
     → (u : ∀ i → Partial (φ ∨ ~ i) (A i))
     → A i
fill A φ i u = comp (λ j → A (i ∧ j)) (φ ∨ ~ i) λ where
  j (φ = i1) → u (i ∧ j) 1=1
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1

open import Agda.Builtin.Cubical.Path public
  using (PathP)
  renaming (_≡_ to _＝_)

Path : (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ _ → A)

module _ {A : Type ℓ} where
  refl : {x : A} → x ＝ x
  refl {x = x} = λ _ → x

  sym : {x y : A} → x ＝ y → y ＝ x
  sym p i = p (~ i)

  cong : {B : A → Type ℓ′} {x y : A}
         (f : (a : A) → B a) (p : x ＝ y)
       → PathP (λ i → B (p i)) (f x) (f y)
  cong f p i = f (p i)

transport : {A B : Type ℓ} → A ＝ B → A → B
transport p = transp (λ i → p i) i0
