{-# OPTIONS --safe #-}
module Data.List.Correspondences.Binary.OPE where

open import Meta.Prelude

open import Data.Empty.Base
open import Data.Nat.Order.Base
open import Data.Reflects
open import Data.List.Base
open import Data.List.Operations

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

¬ope-cons-nil : ∀ {x} {xs : List A} → ¬ OPE (x ∷ xs) []
¬ope-cons-nil ()

ope-length : {xs ys : List A} → OPE xs ys → length xs ≤ length ys
ope-length  odone      = z≤
ope-length (otake _ l) = s≤s (ope-length l)
ope-length (odrop l)   = ≤-trans (ope-length l) ≤-ascend

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
ope-trans  oxy                      odone          = oxy
ope-trans (otake {x} {xs} exy oxy) (otake eyz oyz) = otake (exy ∙ eyz) (ope-trans oxy oyz)
ope-trans (odrop oxy)              (otake eyz oyz) = odrop (ope-trans oxy oyz)
ope-trans  oxy                     (odrop oyz)     = odrop (ope-trans oxy oyz)

ope-antisym : {xs ys : List A}
            → OPE xs ys → OPE ys xs → xs ＝ ys
ope-antisym  odone           _            = refl
ope-antisym (otake exy oxy) (otake _ oyx) = ap² _∷_ exy (ope-antisym oxy oyx)
ope-antisym (otake _ oxy)   (odrop oyx)   = false! $ ≤-trans (ope-length oyx) (ope-length oxy)
ope-antisym (odrop oxy)     (otake _ oyx) = false! $ ≤-trans (ope-length oxy) (ope-length oyx)
ope-antisym (odrop oxy)     (odrop oyx)   = false! $ ≤≃≤+r {n = 2} ⁻¹ $ ≤-trans (s≤s $ ope-length oxy) (ope-length oyx)
