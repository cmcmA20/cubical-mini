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
symₚ p i = p (~ i)

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


congPᴱ
  : {@0 A : Type ℓ} {@0 x y : A} {@0 p : x ＝ y}
    {@0 B : A → Type ℓ′} {@0 b₁ : B x} {@0 b₂ : B y}
  → Erased ＜ b₁ ／ (λ i → B (p i)) ＼ b₂ ＞
  → ＜ erase b₁ ／ (λ i → Erased (B (p i))) ＼ erase b₂ ＞
congPᴱ q i = erase (q .erased i)

congᴱ
  : {@0 A : Type ℓ} {@0 x y : A}
  → Erased (x ＝ y)
  → erase x ＝ erase y
congᴱ p i = erase (p .erased i)

uncongPᴱ
  : {@0 A : Type ℓ} {@0 x y : A} {@0 p : x ＝ y}
    {@0 B : A → Type ℓ′} {@0 b₁ : B x} {@0 b₂ : B y}
  → ＜ erase b₁ ／ (λ i → Erased (B (p i))) ＼ erase b₂ ＞
  → Erased ＜ b₁ ／ (λ i → B (p i)) ＼ b₂ ＞
uncongPᴱ p .erased i = p i .erased

uncongᴱ : {@0 A : Type ℓ} {@0 x y : A}
        → erase x ＝ erase y
        → Erased (x ＝ y)
uncongᴱ p .erased i = p i .erased

substᴱ
  : {@0 A : Type ℓ} (B : @0 A → Type ℓ′)
    {@0 x y : A} (p : Erased (x ＝ y)) → B x → B y
substᴱ B p b = transport (λ i → B (p .erased i)) b
