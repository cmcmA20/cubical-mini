{-# OPTIONS --safe #-}
module Foundations.Isomorphism where

open import Foundations.Prelude
open import Foundations.Equiv.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″

_is-left-inverse-of_ : (B → A) → (A → B) → Type _
g is-left-inverse-of f = (x : _) → g (f x) ＝ x
retraction = _is-left-inverse-of_

_is-right-inverse-of_ : (B → A) → (A → B) → Type _
g is-right-inverse-of f = (y : _) → f (g y) ＝ y
section = _is-right-inverse-of_

record is-iso (f : A → B) : Type (level-of-type A ⊔ level-of-type B) where
  no-eta-equality
  constructor iso
  field
    inv  : B → A
    rinv : inv is-right-inverse-of f
    linv : inv is-left-inverse-of  f

  inverse : is-iso inv
  inv  inverse = f
  rinv inverse = linv
  linv inverse = rinv

  forward-injective : (x y : A) (p : f x ＝ f y) → x ＝ y
  forward-injective x y p = sym (linv x) ∙∙ cong inv p ∙∙ linv y

  inverse-injective : (x y : B) (p : inv x ＝ inv y) → x ＝ y
  inverse-injective x y p = sym (rinv x) ∙∙ cong f p ∙∙ rinv y

open is-iso public

Iso : Type ℓ → Type ℓ′ → Type _
Iso A B = Σ (A → B) is-iso
_≅_ = Iso

idᵢ : Iso A A
idᵢ = id , iso id (λ _ → refl) (λ _ → refl)

_ᵢ⁻¹ : Iso A B → Iso B A
𝔯 ᵢ⁻¹ = 𝔯 .snd .inv , inverse (𝔯 .snd)

is-iso-comp : {f : A → B} {g : B → C} → is-iso f → is-iso g → is-iso (g ∘ f)
is-iso-comp     r s .inv    = r .inv ∘ s .inv
is-iso-comp {g} r s .rinv z = cong g        (r .rinv (s .inv z)) ∙ s .rinv z
is-iso-comp {f} r s .linv x = cong (r .inv) (s .linv (f      x)) ∙ r .linv x

_∙ᵢ_ : Iso A B → Iso B C → Iso A C
𝔯 ∙ᵢ 𝔰 = 𝔰 .fst ∘ 𝔯 .fst , is-iso-comp (𝔯 .snd) (𝔰 .snd)

id-composition→Iso : {f : A → B} (r : is-iso f) (g : B → A) (p : f ∘ g ＝ id) → is-iso g
id-composition→Iso {f} r g p .inv = f
id-composition→Iso {f} r g p .rinv y = sym (r .linv (g (f y))) ∙∙ cong (λ φ → r .inv (φ (f y))) p ∙∙ r .linv y
id-composition→Iso     r g p .linv y = ap (_$ y) p

is-equiv→is-iso : {f : A → B} → is-equiv f → is-iso f
is-iso.inv  (is-equiv→is-iso eqv) = equiv→inverse eqv
is-iso.rinv (is-equiv→is-iso eqv) y = eqv .equiv-proof y .fst .snd
is-iso.linv (is-equiv→is-iso {f} eqv) x i = eqv .equiv-proof (f x) .snd (x , refl) i .fst
