{-# OPTIONS --safe #-}
module Data.List.Correspondences.Binary.OPE where

open import Meta.Prelude

open import Data.Empty.Base
open import Data.List.Base

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ ℓ′ ℓ″ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  P Q R : A → B → 𝒰 ℓ
  x : A
  y : B
  @0 xs : List A
  @0 ys : List B
  @0 zs : List C

-- aka thinning

data OPE {ℓᵃ} {A : 𝒰 ℓᵃ}
         : List A → List A → 𝒰 ℓᵃ where
  odone : OPE [] []
  otake : ∀ {x y xs ys} → x ＝ y → OPE xs ys → OPE (x ∷ xs) (y ∷ ys)
  odrop : ∀ {xs y ys} → OPE xs ys → OPE xs (y ∷ ys)

ope-nil-l : {xs : List A} → OPE [] xs
ope-nil-l {xs = []}     = odone
ope-nil-l {xs = x ∷ xs} = odrop ope-nil-l

ope-uncons : ∀ {x y} {xs ys : List A}
           → OPE (x ∷ xs) (y ∷ ys) → OPE xs ys
ope-uncons               (otake _ o) = o
ope-uncons {ys = y ∷ ys} (odrop o)   = odrop (ope-uncons o)

ope-refl : {xs : List A}
         → OPE xs xs
ope-refl {xs = []}     = odone
ope-refl {xs = x ∷ xs} = otake refl ope-refl

ope-trans : {xs ys zs : List A}
          → OPE xs ys → OPE ys zs → OPE xs zs
ope-trans                  {ys = .[]}       {zs = .[]}        oxy                      odone                                              = oxy
ope-trans {xs = .(x ∷ xs)} {ys = .(y ∷ ys)} {zs = .(z ∷ zs)} (otake {x} {xs} exy oxy) (otake {x = y} {y = z} {xs = ys} {ys = zs} eyz oyz) = otake (exy ∙ eyz) (ope-trans oxy oyz)
ope-trans                  {ys = .(y ∷ ys)} {zs = .(z ∷ zs)} (odrop oxy)              (otake {x = y} {y = z} {xs = ys} {ys = zs} eyz oyz) = odrop (ope-trans oxy oyz)
ope-trans                                   {zs = .(z ∷ zs)}  oxy                     (odrop {y = z} {ys = zs} oyz)                       = odrop (ope-trans oxy oyz)

¬ope-cons-nil : ∀ {x} {xs : List A} → ¬ OPE (x ∷ xs) []
¬ope-cons-nil ()
