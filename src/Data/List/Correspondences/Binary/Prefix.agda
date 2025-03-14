{-# OPTIONS --safe #-}
module Data.List.Correspondences.Binary.Prefix where

open import Meta.Prelude
open import Meta.Extensionality
open Variadics _

open import Data.List.Base
open import Data.List.Path
open import Data.List.Properties
open import Data.List.Operations

open import Data.Empty.Base
open import Data.Reflects.Base
open import Data.Nat.Base
open import Data.Nat.Order.Base
open import Data.Acc.Base

private variable
  ℓᵃ ℓ : Level
  A : Type ℓᵃ
  x y : A
  xs ys zs ts : List A

opaque
  Prefix Prefix1 : Corr _ (List A , List A) (level-of-type A)

  Prefix {A} xs ys = Σ[ ts ꞉ List A ] (xs ++ ts ＝ ys)
  Prefix1 {A} xs ys = Σ[ t ꞉ A ] Σ[ ts ꞉ List A ] (xs ++ t ∷ ts ＝ ys)

opaque
  unfolding Prefix

  []-prefix : Prefix [] ys
  []-prefix {ys} = ys , refl

  ∷-prefix : x ＝ y → Prefix xs ys → Prefix (x ∷ xs) (y ∷ ys)
  ∷-prefix e (ts , et) = ts , ap² _∷_ e et

  prefix-peel : Prefix (x ∷ xs) (y ∷ ys) → (x ＝ y) × Prefix xs ys
  prefix-peel (ts , et) = ∷-head-inj et , ts , ∷-tail-inj et

  prefix-refl : Prefix xs xs
  prefix-refl {xs} = [] , ++-id-r xs

  prefix-trans : Prefix xs ys → Prefix ys zs → Prefix xs zs
  prefix-trans {xs} (txy , exy) (tyz , eyz) =
    txy ++ tyz , ++-assoc xs txy tyz ⁻¹ ∙ ap (_++ tyz) exy ∙ eyz

  prefix-antisym : Prefix xs ys → Prefix ys xs → xs ＝ ys
  prefix-antisym {xs}      ([]      , exy) (tyx     , eyx) = ++-id-r xs ⁻¹ ∙ exy
  prefix-antisym      {ys} (p ∷ txy , exy) ([]      , eyx) = eyx ⁻¹ ∙ ++-id-r ys
  prefix-antisym {xs}      (p ∷ txy , exy) (q ∷ tyx , eyx) =
    false! $ ++-assoc xs (p ∷ txy) (q ∷ tyx) ⁻¹ ∙ subst (λ w → w ++ q ∷ tyx ＝ xs) (exy ⁻¹) eyx

  prefix-++-l : Prefix (xs ++ zs) ys → Prefix xs ys
  prefix-++-l {xs} {zs} (ts , et) = (zs ++ ts) , (++-assoc xs zs ts ⁻¹ ∙ et)

-- strict

opaque
  unfolding Prefix1
  
  []-prefix1 : Prefix1 [] (y ∷ ys)
  []-prefix1 {y} {ys} = y , ys , refl

  ∷-prefix1 : x ＝ y → Prefix1 xs ys → Prefix1 (x ∷ xs) (y ∷ ys)
  ∷-prefix1 e (t , ts , et) = t , ts , ap² _∷_ e et

  prefix1-peel : Prefix1 (x ∷ xs) (y ∷ ys) → (x ＝ y) × Prefix1 xs ys
  prefix1-peel (t , ts , et) = ∷-head-inj et , t , ts , ∷-tail-inj et

  ¬prefix1-[] : ¬ Prefix1 xs []
  ¬prefix1-[] {xs = []}     (t , ts , et) = false! et
  ¬prefix1-[] {xs = x ∷ xs} (t , ts , et) = false! et

  prefix1-irr : ¬ Prefix1 xs xs
  prefix1-irr (t , ts , et) = false! et

  prefix1-trans : Prefix1 xs ys → Prefix1 ys zs → Prefix1 xs zs
  prefix1-trans {xs} (txy , txys , exy) (tyz , tyzs , eyz) =
      txy
    , txys ++ tyz ∷ tyzs
    , ++-assoc xs (txy ∷ txys) (tyz ∷ tyzs) ⁻¹ ∙ ap (_++ tyz ∷ tyzs) exy ∙ eyz

  prefix1-++-l : Prefix1 (xs ++ zs) ys → Prefix1 xs ys
  prefix1-++-l {xs} {zs = []}     (t , ts , et) =
      t , ts
    , ap (_++ t ∷ ts) (++-id-r xs ⁻¹) ∙ et
  prefix1-++-l {xs} {zs = z ∷ zs} (t , ts , et) =
      z , zs ++ t ∷ ts
    , ++-assoc xs (z ∷ zs) (t ∷ ts) ⁻¹ ∙ et

prefix1-acc : Prefix1 xs (y ∷ ys) → Acc Prefix1 ys → Acc Prefix1 xs
prefix1-acc {xs = []}     xyp  a        =
  acc λ y ypr → absurd (¬prefix1-[] ypr) 
prefix1-acc {xs = x ∷ xs} xyp (acc rec) =
  acc λ y ypr → prefix1-acc ypr (rec xs (prefix1-peel xyp .snd))

prefix1-wf : {A : 𝒰 ℓᵃ} → is-wf (Prefix1 {A = A})
prefix1-wf []       = acc λ y ih → absurd (¬prefix1-[] ih)
prefix1-wf (x ∷ xs) = acc λ y ih → prefix1-acc ih (prefix1-wf xs)
