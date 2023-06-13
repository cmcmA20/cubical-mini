{-# OPTIONS --safe #-}
module Structures.n-Type where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel
open import Foundations.Sigma
open import Foundations.Univalence.Base

open import Meta.HLevel.Base public
open import Meta.Underlying  public

record n-Type ℓ n : Type (ℓsuc ℓ) where
  no-eta-equality
  constructor el
  field
    typ   : Type ℓ
    is-tr : is-of-hlevel n typ
  instance
    H-Level-n-type : ∀ {k} → H-Level (n + k) typ
    H-Level-n-type = basic-instance n is-tr

open n-Type public
  using (H-Level-n-type)
open n-Type using (typ; is-tr)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  n : HLevel
  X Y : n-Type ℓ n

instance
  Underlying-n-Type : Underlying (n-Type ℓ n)
  Underlying-n-Type {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-n-Type .⌞_⌟ = n-Type.typ

@0 ＝-is-of-hlevel : (n : ℕ) → is-of-hlevel n A → is-of-hlevel n B → is-of-hlevel n (A ＝ B)
＝-is-of-hlevel n Ahl Bhl = is-equiv→is-of-hlevel n ua univalence⁻¹ (≃-is-of-hlevel n Ahl Bhl)

n-path : ⌞ X ⌟ ＝ ⌞ Y ⌟ → X ＝ Y
n-path f i .typ = f i
n-path {X} {Y} f i .is-tr =
  is-prop→pathP (λ i → is-of-hlevel-is-prop {A = f i} _) (X .is-tr) (Y .is-tr) i

@0 n-ua : ⌞ X ⌟ ≃ ⌞ Y ⌟ → X ＝ Y
n-ua f = n-path (ua f)

@0 n-univalence : {X Y : n-Type ℓ n} → (⌞ X ⌟ ≃ ⌞ Y ⌟) ≃ (X ＝ Y)
n-univalence {n} {X} {Y} = n-ua , is-iso→is-equiv isic where
  inv : ∀ {Y} → X ＝ Y → ⌞ X ⌟ ≃ ⌞ Y ⌟
  inv p = path→equiv (ap typ p)

  linv : ∀ {Y} → (inv {Y}) is-left-inverse-of n-ua
  linv x = Σ-prop-path is-equiv-is-prop (fun-ext λ x → transport-refl _)

  rinv : ∀ {Y} → (inv {Y}) is-right-inverse-of n-ua
  rinv = J (λ y p → n-ua (inv p) ＝ p) path where
    path : n-ua (inv {X} refl) ＝ refl
    path i j .typ = ua.ε refl i j
    path i j .is-tr = is-prop→SquareP
      (λ i j → is-of-hlevel-is-prop
        {A = ua.ε {A = ⌞ X ⌟} refl i j } n)
      (λ j → X .is-tr) (λ j → n-ua {X = X} {Y = X} (path→equiv refl) j .is-tr)
      (λ j → X .is-tr) (λ j → X .is-tr)
      i j

  isic : is-iso n-ua
  isic = iso inv rinv (linv {Y})

@0 n-Type-is-of-hlevel : ∀ n → is-of-hlevel (suc n) (n-Type ℓ n)
n-Type-is-of-hlevel zero x y = n-ua
  ((λ _ → y .is-tr .fst) , is-contr→is-equiv (x .is-tr) (y .is-tr))
n-Type-is-of-hlevel (suc n) x y =
  is-of-hlevel-≃ (suc n) (n-univalence ₑ⁻¹) (≃-is-of-hlevel (suc n) (x .is-tr) (y .is-tr))

Prop : ∀ ℓ → Type (ℓsuc ℓ)
Prop ℓ = n-Type ℓ 1

Set : ∀ ℓ → Type (ℓsuc ℓ)
Set ℓ = n-Type ℓ 2

instance
  @0 H-Level-nType : ∀ {n k} → H-Level (1 + k + n) (n-Type ℓ k)
  H-Level-nType {k} = basic-instance (1 + k) (n-Type-is-of-hlevel k)

  H-Level-is-equiv
    : {f : A → B} {n : HLevel}
    → H-Level (suc n) (is-equiv f)
  H-Level-is-equiv = prop-instance (is-equiv-is-prop _)


-- module _ {ℓ : Level} {n : HLevel} where private
--   open import Foundations.Univalence.SIP
--   _ : n-Type ℓ n ≃ Type-with {S = is-of-hlevel n} (HomT→Str λ _ _ _ → ⊤)
--   _ = iso→equiv the-iso
--     where
--       open import Meta.Reflection.Record
--       the-iso : Iso (n-Type ℓ n) (Σ[ T ꞉ Type ℓ ] is-of-hlevel n T)
--       unquoteDef the-iso = define-record-iso the-iso (quote n-Type)
