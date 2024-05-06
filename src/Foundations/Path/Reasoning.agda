{-# OPTIONS --safe #-}
module Foundations.Path.Reasoning where

open import Foundations.Base
open import Foundations.Path.Groupoid

private variable
  ℓ : Level
  A : Type ℓ
  x x′ y y′ z z′ w w′ : A
  p p′ q q′ r r′ s s′ t : x ＝ y

opaque
  unfolding _∙ₚ_

  -- TODO draw this and reorder args
  pasteP
    : ∀ {α β γ δ}
    → Square α p β p′
    → Square α q γ q′
    → Square β r δ r′
    → Square γ s δ s′
    → Square {a₀₀ = w } {a₀₁ = x } p  {a₁₀ = z } q {a₁₁ = y } s  r
    → Square {a₀₀ = w′} {a₀₁ = x′} p′ {a₁₀ = z′} q′{a₁₁ = y′} s′ r′
  pasteP top left right bottom square i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → left   k j
    k (i = i1) → right  k j
    k (j = i0) → top    k i
    k (j = i1) → bottom k i
    k (k = i0) → square i j

  ∙-id-comm : {A : Type ℓ} {x y : A} {p : x ＝ y}
            → p ∙ refl ＝ refl ∙ p
  ∙-id-comm {p} i j =
    hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → ∙-filler-l p refl k j
      k (i = i1) → ∙-filler-l refl p k j
      k (j = i0) → p i0
      k (j = i1) → p (~ i ∨ k)
      k (k = i0) → p (~ i ∧ j)

  paste : p ＝ p′ → q ＝ q′ → r ＝ r′ → s ＝ s′
        → Square p  q  r  s
        → Square p′ q′ r′ s′
  paste p q r s = pasteP p q s r

module _ {A : Type ℓ} {y : A} {p : y ＝ y} (p＝refl : p ＝ refl) where opaque
  ∙-elim-l : {q : y ＝ z} → p ∙ q ＝ q
  ∙-elim-l {q} = sym $ paste (ap sym p＝refl) refl refl refl (∙-filler-r p q)

  ∙-elim-r : {q : x ＝ y} → q ∙ p ＝ q
  ∙-elim-r {q} = sym $ paste refl refl p＝refl refl (∙-filler-l q p)

  ∙-intro-l : {q : y ＝ z} → q ＝ p ∙ q
  ∙-intro-l = sym ∙-elim-l

  ∙-intro-r : {q : x ＝ y} → q ＝ q ∙ p
  ∙-intro-r = sym ∙-elim-r


module _ {A : Type ℓ} {x y z : A}
  {p : x ＝ y} {q : y ＝ z} {s : x ＝ z} (pq＝s : p ∙ q ＝ s) where opaque

  ∙-pull-l : {w : A} {r : z ＝ w} → p ∙ q ∙ r ＝ s ∙ r
  ∙-pull-l {r} = ∙-assoc p q r ∙ ap (_∙ r) pq＝s

  double-left : {w : A} {r : z ＝ w} → p ∙∙ q ∙∙ r ＝ s ∙ r
  double-left {r} = ∙∙=∙ p q r ∙ ∙-pull-l

  ∙-pull-r : {w : A} {r : w ＝ x} → (r ∙ p) ∙ q ＝ r ∙ s
  ∙-pull-r {r} = sym (∙-assoc r p q) ∙ ap (r ∙_) pq＝s

module _
  {A : Type ℓ} {x y z : A}
  {p : x ＝ y} {q : y ＝ z} {s : x ＝ z} (s＝pq : s ＝ p ∙ q) where opaque
  ∙-push-l : {w : A} {r : z ＝ w} → s ∙ r ＝ p ∙ q ∙ r
  ∙-push-l = sym (∙-pull-l (sym s＝pq))

  ∙-push-r : {w : A} {r : w ＝ x} → r ∙ s ＝ (r ∙ p) ∙ q
  ∙-push-r = sym (∙-pull-r (sym s＝pq))

  double-right : {w : A} {r : w ＝ x} → r ∙∙ p ∙∙ q ＝ r ∙ s
  double-right {r} = ∙∙=∙ r p q ∙ ap (r ∙_) (sym s＝pq)

module _
  {A : Type ℓ} {x y z w : A}
  {p : x ＝ y} {q : y ＝ z} {r : x ＝ w} {s : w ＝ z} (pq=rs : p ∙ₚ q ＝ r ∙ₚ s) where opaque
  ∙-extend-l : {u : A} {t : z ＝ u} → p ∙ (q ∙ t) ＝ r ∙ (s ∙ t)
  ∙-extend-l {t} = ∙-assoc _ _ _ ∙∙ ap (_∙ t) pq=rs ∙∙ ∙-assoc _ _ _ ⁻¹

  ∙-extend-r : {u : A} {t : u ＝ x} → (t ∙ p) ∙ q ＝ (t ∙ r) ∙ s
  ∙-extend-r {t} = ∙-assoc _ _ _ ⁻¹ ∙∙ ap (t ∙_) pq=rs ∙∙ ∙-assoc _ _ _

module _ {A : Type ℓ} {x y : A} {p : x ＝ y} {q : y ＝ x} (inv : p ∙ q ＝ refl) where opaque
  ∙-cancel-l′ : {z : A} {r : x ＝ z} → p ∙ (q ∙ r) ＝ r
  ∙-cancel-l′ = ∙-pull-l inv ∙ ∙-id-l _

  ∙-cancel-r′ : {z : A} {r : z ＝ x} → (r ∙ p) ∙ q ＝ r
  ∙-cancel-r′ = ∙-pull-r inv ∙ ∙-id-r _

  ∙-insert-l : {z : A} {r : x ＝ z} → r ＝ p ∙ (q ∙ r)
  ∙-insert-l = sym ∙-cancel-l′

  ∙-insert-r : {z : A} {r : z ＝ x} → r ＝ (r ∙ p) ∙ q
  ∙-insert-r = sym ∙-cancel-r′

_⟩∙⟨_ : {A : Type ℓ} {x y z : A} {p q : x ＝ y} {r s : y ＝ z}
      → p ＝ q → r ＝ s → p ∙ r ＝ q ∙ s
_⟩∙⟨_ p q i = p i ∙ q i

refl⟩∙⟨_ : {A : Type ℓ} {x y z : A} {p q : x ＝ y} {r : z ＝ x}
         → p ＝ q → r ∙ p ＝ r ∙ q
refl⟩∙⟨_ {r} p = ap (r ∙_) p

_⟩∙⟨refl : {A : Type ℓ} {x y z : A} {p q : x ＝ y} {r : y ＝ z}
         → p ＝ q → p ∙ r ＝ q ∙ r
_⟩∙⟨refl {r} p = ap (_∙ r) p
