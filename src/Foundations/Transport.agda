{-# OPTIONS --safe #-}
module Foundations.Transport where

open import Foundations.Base
open import Foundations.Equiv.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A B C : Type ℓ
  x y z w : A

transport-filler-ext : (p : A ＝ B)
                     → ＜ id ／ (λ i → A → p i) ＼ transport p ＞
transport-filler-ext p i x = transport-filler p x i

transport⁻-filler-ext : {A B : Type ℓ} (p : A ＝ B)
                      → ＜ id ／ (λ i → p i → A) ＼ transport (sym p) ＞
transport⁻-filler-ext p i = coei→0 (λ j → p j) i

transport⁻-transport : {A B : Type ℓ} (p : A ＝ B) (a : A)
                     → transport (sym p) (transport p a) ＝ a
transport⁻-transport p a i =
  transport⁻-filler-ext p (~ i) (transport-filler-ext p (~ i) a)

transport-comp : {A B : Type ℓ} (p : A ＝ B) (q : B ＝ C) (x : A)
               → transport (p ∙ q) x ＝ transport q (transport p x)
transport-comp p q x i = transport (∙-filler-r p q (~ i)) (transport-filler-ext p i x)

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

subst⁻-filler : {A : Type ℓ} (B : A → Type ℓ′) {x y : A} (p : x ＝ y) (b : B y)
              → ＜ b ／ (λ i → B (p (~ i))) ＼ subst B (sym p) b ＞
subst⁻-filler B p = subst-filler B (sym p)

subst⁻-subst : {A : Type ℓ} (B : A → Type ℓ′) {x y : A} (p : x ＝ y)
             → (u : B x) → subst B (sym p) (subst B p u) ＝ u
subst⁻-subst B p u = transport⁻-transport (ap B p) u


subst² : {B : Type ℓ′} {z w : B} (C : A → B → Type ℓ″)
         (p : x ＝ y) (q : z ＝ w) → C x z → C y w
subst² B p q = transport (λ i → B (p i) (q i))

subst²-filler : {B : Type ℓ′} {z w : B} (C : A → B → Type ℓ″)
                (p : x ＝ y) (q : z ＝ w) (c : C x z)
              → ＜ c ／ (λ i → C (p i) (q i)) ＼ subst² C p q c ＞
subst²-filler C p q = transport-filler (ap² C p q)

subst-comp : {A : Type ℓ} (B : A → Type ℓ′)
             {x y z : A} (p : x ＝ y) (q : y ＝ z) (u : B x)
           → subst B (p ∙ q) u ＝ subst B q (subst B p u)
subst-comp B p q Bx i =
  transport (ap B (∙-filler-r p q (~ i))) (transport-filler-ext (ap B p) i Bx)

subst-slice : {A : Type ℓ} (B : A → Type ℓ′) (C : A → Type ℓ″)
              (F : ∀[ a ꞉ A ] (B a → C a))
              {x y : A} (p : x ＝ y) (b : B x)
            → subst C p (F b) ＝ F (subst B p b)
subst-slice B C F p b i = (symᴾ $ transport⁻-filler-ext $ ap C (sym p)) i $ₜ
  F {p i} (transport-filler-ext (ap B p) i b)

subst-slice-filler : {ℓ ℓ′ ℓ″ : Level}
                     {A : Type ℓ} (B : A → Type ℓ′) (C : A → Type ℓ″)
                     (F : ∀[ a ꞉ A ] (B a → C a))
                     {x y : A} (p : x ＝ y)
                   → ＜ F ／ (λ i → B (p i) → C (p i)) ＼ subst C p ∘ F ∘ subst B (sym p) ＞
subst-slice-filler B C F p i b = transport-filler (ap C p)
  (F (transport⁻-filler-ext (ap B p) i b)) i

subst-equiv : (P : A → Type ℓ′) (p : x ＝ y) → P x ≃ P y
subst-equiv P p = subst P p , transport-is-equiv (λ i → P (p i))
