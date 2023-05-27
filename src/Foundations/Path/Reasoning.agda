{-# OPTIONS --safe #-}
module Foundations.Path.Reasoning where

open import Foundations.Base
open import Foundations.Path.Groupoid

private variable
  ℓ : Level
  A : Type ℓ
  x x′ y y′ z z′ w w′ : A
  p p′ q q′ r r′ s s′ t : x ＝ y

∙-filler″ : (p : x ＝ y) (q : y ＝ z)
          → Square refl (sym p) (p ∙ q) q
∙-filler″ {y} p q i j =
  hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p (~ j)
    k (i = i1) → q (j ∧ k)
    k (j = i0) → y
    k (k = i0) → p (i ∨ ~ j)

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

paste : p ＝ p′ → q ＝ q′ → r ＝ r′ → s ＝ s′
      → Square p  q  r  s
      → Square p′ q′ r′ s′
paste p q r s = pasteP p q s r

∙-id-comm : p ∙ refl ＝ refl ∙ p
∙-id-comm {p} i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → ∙-filler  p refl k j
    k (i = i1) → ∙-filler″ refl p j k
    k (j = i0) → p i0
    k (j = i1) → p (~ i ∨ k)
    k (k = i0) → p (~ i ∧ j)


module _ (p＝refl : p ＝ refl) where
  ∙-elim-l : p ∙ q ＝ q
  ∙-elim-l {q} = sym $ paste (ap sym p＝refl) refl refl refl (∙-filler′ p q)

  ∙-elim-r : q ∙ p ＝ q
  ∙-elim-r {q} = sym $ paste refl refl p＝refl refl (∙-filler q p)

  ∙-intro-l : q ＝ p ∙ q
  ∙-intro-l = sym ∙-elim-l

  ∙-intro-r : q ＝ q ∙ p
  ∙-intro-r = sym ∙-elim-r


module _ (pq＝s : p ∙ q ＝ s) where
  ∙-pull-l : p ∙ q ∙ r ＝ s ∙ r
  ∙-pull-l {r} = ∙-assoc p q r ∙ ap (_∙ r) pq＝s

  double-left : p ∙∙ q ∙∙ r ＝ s ∙ r
  double-left {r} = double-composite p q r ∙ ∙-pull-l

  ∙-pull-r : (r ∙ p) ∙ q ＝ r ∙ s
  ∙-pull-r {r} = sym (∙-assoc r p q) ∙ ap (r ∙_) pq＝s

module _ (s＝pq : s ＝ p ∙ q) where
  ∙-push-l : s ∙ r ＝ p ∙ q ∙ r
  ∙-push-l = sym (∙-pull-l (sym s＝pq))

  ∙-push-r : r ∙ s ＝ (r ∙ p) ∙ q
  ∙-push-r = sym (∙-pull-r (sym s＝pq))

module _ (pq＝rs : p ∙ q ＝ r ∙ s) where
  ∙-extend-l : p ∙ (q ∙ t) ＝ r ∙ (s ∙ t)
  ∙-extend-l {t = t} = ∙-assoc _ _ _ ∙∙ ap (_∙ t) pq＝rs ∙∙ sym (∙-assoc _ _ _)

  ∙-extend-r : (t ∙ p) ∙ q ＝ (t ∙ r) ∙ s
  ∙-extend-r {t = t} = sym (∙-assoc _ _ _) ∙∙ ap (t ∙_) pq＝rs ∙∙ ∙-assoc _ _ _

module _ (inv : p ∙ q ＝ refl) where abstract
  ∙-cancel-l′ : p ∙ (q ∙ r) ＝ r
  ∙-cancel-l′ = ∙-pull-l inv ∙ ∙-id-l _

  ∙-cancel-r′ : (r ∙ p) ∙ q ＝ r
  ∙-cancel-r′ = ∙-pull-r inv ∙ ∙-id-r _

  ∙-insert-l : r ＝ p ∙ (q ∙ r)
  ∙-insert-l = sym ∙-cancel-l′

  ∙-insert-r : r ＝ (r ∙ p) ∙ q
  ∙-insert-r = sym ∙-cancel-r′

_⟩∙⟨_ : p ＝ q → r ＝ s → p ∙ r ＝ q ∙ s
_⟩∙⟨_ p q i = p i ∙ q i

refl⟩∙⟨_ : p ＝ q → r ∙ p ＝ r ∙ q
refl⟩∙⟨_ {r} p = ap (r ∙_) p

_⟩∙⟨refl : p ＝ q → p ∙ r ＝ q ∙ r
_⟩∙⟨refl {r} p = ap (_∙ r) p
