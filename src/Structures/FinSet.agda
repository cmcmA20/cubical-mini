{-# OPTIONS --safe #-}
module Structures.FinSet where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Fin.Base
open import Data.Fin.Finite

open import Meta.HLevel
open import Meta.Finite     public
open import Meta.Underlying public

open import Truncation.Propositional

record Fin-Set ℓ : Type (ℓsuc ℓ) where
  no-eta-equality
  constructor fin-set
  field
    typ            : Type ℓ
    has-is-fin-set : is-fin-set typ
  instance
    Finite-Fin-Set : Finite typ
    Finite-Fin-Set = fin $ has-is-fin-set .snd

    H-Level-Fin-Set : ∀ {n} → H-Level (2 + n) typ
    H-Level-Fin-Set = basic-instance 2 (is-fin-set→is-set has-is-fin-set)

open Fin-Set public
  using (Finite-Fin-Set; H-Level-Fin-Set)
open Fin-Set using (typ; has-is-fin-set)

private variable
  ℓ : Level
  A : Type ℓ

instance
  Underlying-Fin-Set : Underlying (Fin-Set ℓ)
  Underlying-Fin-Set {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-Fin-Set .⌞_⌟ = typ


-- TODO
-- fin-set-path : ⌞ X ⌟ ＝ ⌞ Y ⌟ → X ＝ Y
-- fin-set-path f i .typ = f i
-- fin-set-path {X} {Y} f i .has-is-fin-set = {!!} , {!!}
--   -- is-prop→pathP (λ i → is-of-hlevel-is-prop {A = f i} _) (X .is-tr) (Y .is-tr) i

-- @0 fin-set-ua : ⌞ X ⌟ ≃ ⌞ Y ⌟ → X ＝ Y
-- fin-set-ua f = n-path (ua f)

-- @0 fin-set-univalence : {X Y : n-Type ℓ n} → (⌞ X ⌟ ≃ ⌞ Y ⌟) ≃ (X ＝ Y)
-- fin-set-univalence {n} {X} {Y} = n-ua , is-iso→is-equiv isic where
--   inv : ∀ {Y} → X ＝ Y → ⌞ X ⌟ ≃ ⌞ Y ⌟
--   inv p = path→equiv (ap typ p)

--   linv : ∀ {Y} → (inv {Y}) is-left-inverse-of n-ua
--   linv x = Σ-prop-path is-equiv-is-prop (fun-ext λ x → transport-refl _)

--   rinv : ∀ {Y} → (inv {Y}) is-right-inverse-of n-ua
--   rinv = J (λ y p → n-ua (inv p) ＝ p) path where
--     path : n-ua (inv {X} refl) ＝ refl
--     path i j .typ = ua.ε refl i j
--     path i j .is-tr = is-prop→SquareP
--       (λ i j → is-of-hlevel-is-prop
--         {A = ua.ε {A = ⌞ X ⌟} refl i j } n)
--       (λ j → X .is-tr) (λ j → n-ua {X = X} {Y = X} (path→equiv refl) j .is-tr)
--       (λ j → X .is-tr) (λ j → X .is-tr)
--       i j

--   isic : is-iso n-ua
--   isic = iso inv rinv (linv {Y})

-- @0 fin-set-is-of-hlevel : ∀ n → is-of-hlevel (suc n) (n-Type ℓ n)
-- fin-set-is-of-hlevel zero x y = n-ua
--   ((λ _ → y .is-tr .fst) , is-contr→is-equiv (x .is-tr) (y .is-tr))
-- fin-set-is-of-hlevel (suc n) x y =
--   is-of-hlevel-≃ (suc n) (n-univalence ₑ⁻¹) (≃-is-of-hlevel (suc n) (x .is-tr) (y .is-tr))

-- instance
--   @0 H-Level-nType : ∀ {n k} → H-Level (1 + k + n) (n-Type ℓ k)
--   H-Level-nType {k} = basic-instance (1 + k) (n-Type-is-of-hlevel k)

--   H-Level-is-equiv
--     : {f : A → B} {n : HLevel}
--     → H-Level (suc n) (is-equiv f)
--   H-Level-is-equiv = prop-instance (is-equiv-is-prop _)

-- module _ {ℓ : Level} where private
--   open import Foundations.Univalence.SIP
--   _ : Fin-Set ℓ ≃ Type-with {S = is-fin-set} (HomT→Str λ _ _ _ → ⊤)
--   _ = iso→equiv the-iso
--     where
--       open import Meta.Reflection.Record
--       the-iso : Iso (Fin-Set ℓ) (Σ[ T ꞉ Type ℓ ] is-fin-set T)
--       unquoteDef the-iso = define-record-iso the-iso (quote Fin-Set)
