{-# OPTIONS --safe #-}
module Structures.n-Type where

open import Foundations.Base
open import Foundations.Cubes
open import Foundations.Equiv
open import Foundations.HLevel
open import Foundations.Path
open import Foundations.Sigma
open import Foundations.Univalence

open import Meta.Record
open import Meta.Underlying public

open import Structures.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  n : HLevel

record n-Type (ℓ : Level) (n : HLevel) : Type (ℓsuc ℓ) where
  constructor el
  field
    carrier : Type ℓ
    carrier-is-tr : is-of-hlevel n carrier

open n-Type

unquoteDecl n-Type-iso = declare-record-iso n-Type-iso (quote n-Type)

private variable
  X Y : n-Type ℓ n

instance
  Underlying-n-Type : Underlying (n-Type ℓ n)
  Underlying-n-Type {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-n-Type .⌞_⌟ = carrier

n-path : ⌞ X ⌟ ＝ ⌞ Y ⌟ → X ＝ Y
n-path f i .carrier = f i
n-path {X} {Y} f i .carrier-is-tr =
  is-prop→pathP (λ i → is-of-hlevel-is-prop {A = f i} _) (X .carrier-is-tr) (Y .carrier-is-tr) i

-- FIXME rewrite without cubes
n-path-refl : n-path {X = X} refl ＝ refl
n-path-refl {X} _ _ .carrier = X .carrier
n-path-refl {X} i j .carrier-is-tr = θ j i where
  p = is-prop→pathP (λ _ → is-of-hlevel-is-prop _) (X .carrier-is-tr) _
  θ : Square p refl refl refl
  θ = is-prop→squareP (λ _ _ → is-of-hlevel-is-prop _) _ _ _ _

@0 n-ua : ⌞ X ⌟ ≃ ⌞ Y ⌟ → X ＝ Y
n-ua f = n-path (ua f)

opaque
  unfolding univalence⁻¹
  @0 n-univalence : (⌞ X ⌟ ≃ ⌞ Y ⌟) ≃ (X ＝ Y)
  n-univalence {X} {Y} = n-ua , is-iso→is-equiv isic where
    inv : ∀ {Y} → X ＝ Y → ⌞ X ⌟ ≃ ⌞ Y ⌟
    inv p = path→equiv (ap carrier p)

    linv : ∀ {Y} → (inv {Y}) is-left-inverse-of n-ua
    linv x = Σ-prop-path is-equiv-is-prop (fun-ext λ x → transport-refl _)

    rinv : ∀ {Y} → (inv {Y}) is-right-inverse-of n-ua
    rinv = J (λ y p → n-ua (inv p) ＝ p) path where
      path : n-ua {X = X} (inv {X} refl) ＝ refl
      path i j .carrier = ua.ε refl i j
      path i j .carrier-is-tr = is-prop→squareP
        (λ i j → is-of-hlevel-is-prop
          {A = ua.ε {A = ⌞ X ⌟} refl i j } _)
        (λ j → carrier-is-tr $ n-ua {X = X} {Y = X} (path→equiv refl) j)
        (λ _ → carrier-is-tr X)
        (λ _ → carrier-is-tr X)
        (λ _ → carrier-is-tr X)
        i j

    isic : is-iso (n-ua {X = X} {Y = Y})
    isic = iso inv rinv (linv {Y})

-- FIXME disgusting! rewrite it without resorting to direct cube manipulations
opaque
  unfolding _∙_
  @0 n-path-∙ : {A B C : n-Type ℓ n}
                (p : ⌞ A ⌟ ＝ ⌞ B ⌟) (q : ⌞ B ⌟ ＝ ⌞ C ⌟)
              → n-path {X = A} {Y = C} (p ∙ q) ＝ n-path {Y = B} p ∙ n-path q
  n-path-∙ p q i j .carrier = (p ∙ q) j
  n-path-∙ {n} {A} {B} {C} p q j i .carrier-is-tr = θ i j where
    θ : SquareP (λ k _ → is-of-hlevel n ((p ∙ q) k))
          refl (is-prop→pathP (λ _ → is-of-hlevel-is-prop n) (A .carrier-is-tr) (C .carrier-is-tr))
          refl (λ k → (n-path {X = A} {Y = B} p ∙ n-path {Y = C} q) k .carrier-is-tr)
    θ = is-set→squareP (λ _ _ → is-of-hlevel-is-of-hlevel-suc 1) _ _ _ _

@0 n-ua-∙ₑ : {A B C : n-Type ℓ n}
             (f : ⌞ A ⌟ ≃ ⌞ B ⌟) (g : ⌞ B ⌟ ≃ ⌞ C ⌟)
           → n-ua {X = A} {Y = C} (f ∙ₑ g) ＝ n-ua {Y = B} f ∙ n-ua g
n-ua-∙ₑ f g = ap n-path (ua-∙ₑ f g) ∙ n-path-∙ (ua f) (ua g)

opaque
  unfolding is-of-hlevel
  @0 n-Type-is-of-hlevel : ∀ n → is-of-hlevel (suc n) (n-Type ℓ n)
  n-Type-is-of-hlevel zero X Y = n-ua
    ((λ _ → carrier-is-tr Y .fst) , is-contr→is-equiv (X .carrier-is-tr) (Y .carrier-is-tr))
  n-Type-is-of-hlevel (suc n) X Y =
    is-of-hlevel-≃ (suc n) (n-univalence ₑ⁻¹) (≃-is-of-hlevel (suc n) (X .carrier-is-tr) (Y .carrier-is-tr))

Prop : ∀ ℓ → Type (ℓsuc ℓ)
Prop ℓ = n-Type ℓ 1

Set : ∀ ℓ → Type (ℓsuc ℓ)
Set ℓ = n-Type ℓ 2

Grpd : ∀ ℓ → Type (ℓsuc ℓ)
Grpd ℓ = n-Type ℓ 3


-- module _ {ℓ : Level} {n : HLevel} where private
--   open import Foundations.Univalence.SIP
--   _ : n-Type ℓ n ≃ Type-with {S = is-of-hlevel n} (HomT→Str λ _ _ _ → ⊤)
--   _ = iso→equiv n-Type-iso
