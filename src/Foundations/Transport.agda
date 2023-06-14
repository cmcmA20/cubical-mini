{-# OPTIONS --safe #-}
module Foundations.Transport where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.FromPath

private variable
  ℓ ℓ′ ℓ″ : Level
  A B C : Type ℓ
  x y z w : A

transport-filler-ext : (p : A ＝ B)
                     → ＜ id ／ (λ i → A → p i) ＼ transport p ＞
transport-filler-ext p i x = transport-filler p x i

transport⁻-filler-ext : (p : A ＝ B)
                      → ＜ id ／ (λ i → p i → A) ＼ transport (sym p) ＞
transport⁻-filler-ext p i x = transp (λ j → p (i ∧ ~ j)) (~ i) x

transport⁻-transport : (p : A ＝ B) (a : A)
                     → transport (sym p) (transport p a) ＝ a
transport⁻-transport p a i =
  transport⁻-filler-ext p (~ i) (transport-filler-ext p (~ i) a)

transport-comp : (p : A ＝ B) (q : B ＝ C) (x : A)
               → transport (p ∙ q) x ＝ transport q (transport p x)
transport-comp p q x i = transport (∙-filler′ p q (~ i)) (transport-filler-ext p i x)

transport-is-equiv : (p : A ＝ B) → is-equiv (transport p)
transport-is-equiv p = line→is-equiv (λ i → p i)

transport-flip : {A : I → Type ℓ} {x : A i0} {y : A i1}
               → x ＝ transport (λ i → A (~ i)) y
               → transport (λ i → A i) x ＝ y
transport-flip {A} {y} p =
  ap (transport (λ i → A i)) p ∙ transport⁻-transport (λ i → A (~ i)) y


subst-filler : (B : A → Type ℓ′) (p : x ＝ y) (b : B x)
             → ＜ b ／ (λ i → B (p i)) ＼ subst B p b ＞
subst-filler B p = transport-filler (ap B p)

subst⁻-filler : (B : A → Type ℓ′) (p : x ＝ y) (b : B y)
              → ＜ b ／ (λ i → B (p (~ i))) ＼ subst B (sym p) b ＞
subst⁻-filler B p = subst-filler B (sym p)

subst⁻-subst : (B : A → Type ℓ′) (p : x ＝ y)
            → (u : B x) → subst B (sym p) (subst B p u) ＝ u
subst⁻-subst B p u = transport⁻-transport (ap B p) u


subst₂ : {B : Type ℓ′} {z w : B} (C : A → B → Type ℓ″)
         (p : x ＝ y) (q : z ＝ w) → C x z → C y w
subst₂ B p q = transport (λ i → B (p i) (q i))

subst₂-filler : {B : Type ℓ′} {z w : B} (C : A → B → Type ℓ″)
                (p : x ＝ y) (q : z ＝ w) (c : C x z)
              → ＜ c ／ (λ i → C (p i) (q i)) ＼ subst₂ C p q c ＞
subst₂-filler C p q = transport-filler (ap₂ C p q)

subst-comp : (B : A → Type ℓ′)
           → (p : x ＝ y) (q : y ＝ z) (u : B x)
           → subst B (p ∙ q) u ＝ subst B q (subst B p u)
subst-comp B p q Bx i =
  transport (ap B (∙-filler′ p q (~ i))) (transport-filler-ext (ap B p) i Bx)

subst-equiv : (P : A → Type ℓ′) (p : x ＝ y) → P x ≃ P y
subst-equiv P p = subst P p , transport-is-equiv (λ i → P (p i))
