{-# OPTIONS --safe #-}
module Foundations.Prim.Kan where

open import Foundations.Prim.Type
open import Foundations.Prim.Interval
open import Foundations.Prim.Extension

open import Agda.Primitive.Cubical
  using ( primHComp
        ; primComp )

open import Agda.Primitive.Cubical public
  using ()
  renaming ( primTransp to transp )

private variable
  ℓ ℓ′ : Level
  ℓ^ : I → Level
  A : Type ℓ
  B : A → Type ℓ′

hcomp : (φ : I)
      → (u : (i : I) → Partial (φ ∨ ~ i) A)
      → A
hcomp φ u = primHComp (λ j .o → u j (is1-left φ (~ j) o)) (u i0 1=1)

∂ : I → I
∂ i = i ∨ ~ i

comp : (A : (i : I) → Type (ℓ^ i)) (φ : I)
     → (u : (i : I) → Partial (φ ∨ ~ i) (A i))
     → A i1
comp A φ u = primComp A (λ j .o → u j (is1-left φ (~ j) o)) (u i0 1=1)

hfill : (φ : I) → I
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

infix 0 PathP-syntax
PathP-syntax = PathP
syntax PathP-syntax Aᵢ A₀ A₁ = ＜ A₀ ／ Aᵢ ＼ A₁ ＞

Path : (A : Type ℓ) → A → A → Type ℓ
Path A A₀ A₁ = ＜ A₀ ／ (λ _ → A) ＼ A₁ ＞

refl : {x : A} → x ＝ x
refl {x} _ = x

sym : {x y : A} → x ＝ y → y ＝ x
sym p i = p (~ i)

ap : {x y : A}
     (f : (a : A) → B a)
     (p : x         ＝              y)
   → ＜ f x ／ (λ i → B (p i)) ＼ f y ＞
ap f p i = f (p i)

transport : {A B : Type ℓ} → A ＝ B → A → B
transport p = transp (λ i → p i) i0

hcomp-unique : (φ : I)
               (u : ∀ i → Partial (φ ∨ ~ i) A)
             → (h₂ : ∀ i → A [ _ ↦ (λ { (i = i0) → u i0 1=1
                                      ; (φ = i1) → u i  1=1 }) ])
             → hcomp φ u ＝ outS (h₂ i1)
hcomp-unique φ u h₂ i =
  hcomp (φ ∨ i) λ where
    k (k = i0) → u i0 1=1
    k (i = i1) → outS (h₂ k)
    k (φ = i1) → u k 1=1

caseⁱ_of_ : {B : Type ℓ′} (x : A) → ((y : A) → x ＝ y → B) → B
caseⁱ x of f = f x (λ i → x)
{-# INLINE caseⁱ_of_ #-}

caseⁱ_return_of_ : (x : A) (P : A → Type ℓ′) → ((y : A) → x ＝ y → P y) → P x
caseⁱ x return P of f = f x (λ i → x)
{-# INLINE caseⁱ_return_of_ #-}
