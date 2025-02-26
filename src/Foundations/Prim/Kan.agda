{-# OPTIONS --safe #-}
module Foundations.Prim.Kan where

open import Foundations.Prim.Type
open import Foundations.Prim.Interval

open import Agda.Builtin.Sigma
open import Agda.Builtin.Cubical.Sub public
  using ( inS )
  renaming ( Sub to _[_↦_]
           ; primSubOut to outS )

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

partial-pushout
  : {ℓ : Level} (i j : I) {A : Partial (i i∨ j) (Type ℓ)}
    {ai : PartialP {a = ℓ} (i i∧ j) (λ { (j i∧ i = i1) → A 1=1 }) }
  → (.(z : IsOne i) → A (is1-left  i j z) [ (i i∧ j) ↦ (λ { (i i∧ j = i1) → ai 1=1 }) ])
  → (.(z : IsOne j) → A (is1-right i j z) [ (i i∧ j) ↦ (λ { (i i∧ j = i1) → ai 1=1 }) ])
  → PartialP (i i∨ j) A
partial-pushout i j u v = primPOr i j (λ z → outS (u z)) (λ z → outS (v z))

hcomp : (φ : I)
      → (u : (i : I) → Partial (φ i∨ i~ i) A)
      → A
hcomp φ u = primHComp (λ j .o → u j (is1-left φ (i~ j) o)) (u i0 1=1)

∂ : I → I
∂ i = i i∨ i~ i

comp : (A : (i : I) → Type (ℓ^ i)) (φ : I)
     → (u : (i : I) → Partial (φ i∨ i~ i) (A i))
     → A i1
comp A φ u = primComp A (λ j .o → u j (is1-left φ (i~ j) o)) (u i0 1=1)

hfill : (φ : I) → I
      → ((i : I) → Partial (φ i∨ i~ i) A)
      → A
hfill φ i u =
  hcomp (φ i∨ i~ i) λ where
    j (φ = i1) → u (i i∧ j) 1=1
    j (i = i0) → u i0       1=1
    j (j = i0) → u i0       1=1

fill : (A : ∀ i → Type (ℓ^ i)) (φ : I) (i : I)
     → (u : ∀ i → Partial (φ i∨ i~ i) (A i))
     → A i
fill A φ i u = comp (λ j → A (i i∧ j)) (φ i∨ i~ i) λ where
  j (φ = i1) → u (i i∧ j) 1=1
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1

open import Agda.Builtin.Cubical.Path public
  renaming ( _≡_   to _＝_
           ; PathP to Pathᴾ )

infix 0 Pathᴾ-syntax Pathᴾ-syntax′
Pathᴾ-syntax = Pathᴾ

Pathᴾ-syntax′ : ∀ {ℓ} {A B : 𝒰 ℓ} (p : A ＝ B) → A → B → Type ℓ
Pathᴾ-syntax′ p = Pathᴾ (λ i → p i)

syntax Pathᴾ-syntax  Aᵢ A₀ A₁ = ＜ A₀ ／ Aᵢ ＼ A₁ ＞
syntax Pathᴾ-syntax′ Aᵢ A₀ A₁ = A₀ ＝[ Aᵢ ]＝ A₁

Path : (A : Type ℓ) → A → A → Type ℓ
Path A A₀ A₁ = ＜ A₀ ／ (λ _ → A) ＼ A₁ ＞

reflₚ : {x : A} → x ＝ x
reflₚ {x} _ = x

symₚ : {x y : A} → x ＝ y → y ＝ x
symₚ p i = p (i~ i)

ap : {x y : A}
     (f : (a : A) → B a)
     (p : x         ＝              y)
   → ＜ f x ／ (λ i → B (p i)) ＼ f y ＞
ap f p i = f (p i)

transport : {A B : Type ℓ} → A ＝ B → A → B
transport p = transp (λ i → p i) i0

hcomp-unique : (φ : I)
               (u : ∀ i → Partial (φ i∨ i~ i) A)
             → (h₂ : ∀ i → A [ _ ↦ (λ { (i = i0) → u i0 1=1
                                      ; (φ = i1) → u i  1=1 }) ])
             → hcomp φ u ＝ outS (h₂ i1)
hcomp-unique φ u h₂ i =
  hcomp (φ i∨ i) λ where
    k (k = i0) → u i0 1=1
    k (i = i1) → outS (h₂ k)
    k (φ = i1) → u k 1=1

fibre : {A : Type ℓ} {B : Type ℓ′} (f : A → B) (y : B) → Type (ℓ l⊔ ℓ′)
fibre {A} f y = Σ A (λ x → f x ＝ y)

record is-contr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor contr
  no-eta-equality
  field
    centre : A
    paths  : (x : A) → centre ＝ x
{-# INLINE contr #-}

open is-contr public

is-prop : Type ℓ → Type ℓ
is-prop A = (x y : A) → x ＝ y


record Recall {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
  (f : (x : A) → B x) (x : A) (y : B x) : Type (ℓ l⊔ ℓ′) where
  constructor ⟪_⟫
  field eq : f x ＝ y

recall : {A : Type ℓ} {B : A → Type ℓ′}
         (f : (x : A) → B x) (x : A)
       → Recall f x (f x)
recall _ _ = ⟪ reflₚ ⟫
