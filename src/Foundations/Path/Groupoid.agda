{-# OPTIONS --safe #-}
module Foundations.Path.Groupoid where

open import Foundations.Base
open import Foundations.Path.Base
open import Foundations.Transport

private variable
  ℓ ℓ′ : Level

opaque
  unfolding _∙ₚ_

  instance
    HUnit-o-Path : {A : Type ℓ} → HUnit-o (Path A)
    HUnit-o-Path .∙-id-o p = ∙-filler-r refl p ⁻¹

    HUnit-i-Path : {A : Type ℓ} → HUnit-i (Path A)
    HUnit-i-Path .∙-id-i p = ∙-filler-l p refl ⁻¹

    HAssoc-Path : {A : Type ℓ} → HAssoc (Path A)
    HAssoc-Path .∙-assoc p q r i = ∙-filler-l p q i ∙ ∙-filler-r q r (~ i)

    HInv-o-Path : {A : Type ℓ} → HInv-o (Path A)
    HInv-o-Path .∙-inv-o {x} p i j = hcomp (∂ j ∨ i) λ where
      k (j = i0) → p (k ∨ i)
      k (j = i1) → p (k ∨ i)
      k (i = i1) → x
      k (k = i0) → p i

    HInv-i-Path : {A : Type ℓ} → HInv-i (Path A)
    HInv-i-Path .∙-inv-i p = ∙-inv-o (sym p)

  ∙-cancel-l : {A : Type ℓ} {x y z : A}
               (p : x ＝ y) (q : y ＝ z)
             → p ⁻¹ ∙ p ∙ q ＝ q
  ∙-cancel-l {y} p q i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → p (i ∨ ~ j)
    k (i = i0) → ∙-filler-l (sym p) (p ∙ q) k j
    k (i = i1) → q (j ∧ k)
    k (j = i0) → y
    k (j = i1) → ∙-filler-r p q (~ i) k

  ∙-cancel-r : {A : Type ℓ} {x y z : A}
               (p : x ＝ y) (q : z ＝ y)
             → (p ∙ q ⁻¹) ∙ q ＝ p
  ∙-cancel-r q p = sym $ ∙-unique q λ i j → ∙-filler-l p (sym q) (~ j) i

  commutes→square : {A : Type ℓ} {w x y z : A}
                    {p : w ＝ x} {q : w ＝ y} {s : x ＝ z} {r : y ＝ z}
                  → p ∙ s ＝ q ∙ r
                  → Square p q r s
  commutes→square {p} {q} {s} {r} θ i j =
    hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → θ j i
      k (i = i0) → q (  k ∧ j)
      k (i = i1) → s (~ k ∨ j)
      k (j = i0) → ∙-filler-l p s (~ k) i
      k (j = i1) → ∙-filler-r q r (~ k) i

  square→commutes : {A : Type ℓ} {w x y z : A}
                    {p : w ＝ x} {q : w ＝ y} {s : x ＝ z} {r : y ＝ z}
                  → Square p q r s
                  → p ∙ s ＝ q ∙ r
  square→commutes {p} {q} {s} {r} θ i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → θ j i
    k (i = i0) → ∙-filler-l p s k j
    k (i = i1) → ∙-filler-r q r k j
    k (j = i0) → q (~ k ∧ i)
    k (j = i1) → s (k ∨ i)

  square→conjugate
    : {A : Type ℓ} {w x y z : A}
      {p : x ＝ y} {q : x ＝ z} {r : z ＝ w} {s : y ＝ w}
    → Square p q r s
    → s ＝ p ⁻¹ ∙ q ∙ r
  square→conjugate {p} {q} {r} {s} θ =
    sym (ap fst (∙∙-contract _ _ _ (_ , θ))) ∙ ∙∙=∙ _ _ _

  conjugate→square
    : {A : Type ℓ} {w x y z : A}
      {p : x ＝ y} {q : x ＝ z} {r : z ＝ w} {s : y ＝ w}
    → s ＝ p ⁻¹ ∙ q ∙ r
    → Square p q r s
  conjugate→square {p} {q} {r} {s} u =
    to-pathᴾ (transport-path q p r ∙ sym u)

  ∙-cancel′-l : {A : Type ℓ} {x y z : A}
                (p : x ＝ y) (q r : y ＝ z)
              → p ∙ q ＝ p ∙ r
              → q ＝ r
  ∙-cancel′-l p q r sq =
       sym (∙-cancel-l p q)
    ∙∙ sym p ◁ sq
    ∙∙ ∙-cancel-l p r

  ∙-cancel′-r : {A : Type ℓ} {x y z : A}
                (p : y ＝ z) (q r : x ＝ y)
              → q ∙ p ＝ r ∙ p
              → q ＝ r
  ∙-cancel′-r p q r sq =
       sym (∙-cancel-r q (sym p))
    ∙∙ sq ▷ sym p
    ∙∙ ∙-cancel-r r (sym p)

  whisker-path-l : {A : Type ℓ} {x y z : A}
                 → (x ＝ y) → (x ＝ z) ＝ (y ＝ z)
  whisker-path-l {z} p i = p i ＝ z

  whisker-path-r : {A : Type ℓ} {x y z : A}
                 → (y ＝ z) → (x ＝ y) ＝ (x ＝ z)
  whisker-path-r {x} q i = x ＝ q i

  homotopy-invert : {A : Type ℓ} {f : A → A}
                  → (H : Π[ x ꞉ A ] (f x ＝ x)) {x : A}
                  → H (f x) ＝ ap f (H x)
  homotopy-invert {f} H {x} i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → H x       (j ∧ i)
    k (j = i0) → H (f x)   (~ k)
    k (j = i1) → H x       (~ k ∧ i)
    k (i = i0) → H (f x)   (~ k ∨ j)
    k (i = i1) → H (H x j) (~ k)

  homotopy-natural : {A : Type ℓ} {B : Type ℓ′} {f g : A → B}
                     (H : Π[ a ꞉ A ] (f a ＝ g a))
                     {x y : A} (p : x ＝ y)
                   → H x ∙ ap g p ＝ ap f p ∙ H y
  homotopy-natural {f} H {x} p =
    square→commutes λ j i → hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → H x           (j ∧ k)
      k (i = i1) → H (p k)       (j ∧ k)
      k (j = i0) → f (p (i ∧ k))
      k (j = i1) → H (p (i ∧ k)) k
      k (k = i0) → f x

  homotopy-sym-inv : {A : Type ℓ} {f : A → A}
                     (H : Π[ a ꞉ A ] (f a ＝ a))
                     (x : A)
                   → Path (f x ＝ f x) (λ i → H (H x (~ i)) i) refl
  homotopy-sym-inv {f} H x i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → H (H x (~ j)) j
    k (i = i1) → H x (j ∧ ~ k)
    k (j = i0) → f x
    k (j = i1) → H x (i ∧ ~ k)
    k (k = i0) → H (H x (i ∨ ~ j)) j
