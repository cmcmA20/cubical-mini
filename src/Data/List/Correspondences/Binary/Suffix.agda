{-# OPTIONS --safe #-}
module Data.List.Correspondences.Binary.Suffix where

open import Meta.Prelude

open import Data.List.Base
open import Data.List.Path
open import Data.List.Properties
open import Data.List.Operations
open import Data.List.Operations.Properties
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Membership

open import Data.Empty.Base
open import Data.Empty.Properties as ⊥
open import Data.Reflects.Base
open import Data.Nat.Order.Base
open import Data.Acc.Base

private variable
  ℓᵃ ℓᵇ ℓ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  x y : A
  xs ys zs ts : List A

opaque
  Suffix Suffix1 : Corr² (List A , List A) (level-of-type A)

  Suffix {A} xs ys = Σ[ ts ꞉ List A ] (ts ++ xs ＝ ys)
  Suffix1 {A} xs ys = Σ[ t ꞉ A ] Σ[ ts ꞉ List A ] (ts ++ t ∷ xs ＝ ys)

-- TODO add more

opaque
  unfolding Suffix Suffix1

  []-suffix : Suffix [] ys
  []-suffix {ys} = ys , ++-id-r ys

  ¬-suffix1-[] : ¬ Suffix1 xs []
  ¬-suffix1-[] (t , []     , e) = false! e
  ¬-suffix1-[] (t , x ∷ ts , e) = false! e

  =→suffix : xs ＝ ys → Suffix xs ys
  =→suffix exy = [] , exy

  suffix-refl : Suffix xs xs
  suffix-refl = =→suffix refl

  suffix-trans : Suffix xs ys → Suffix ys zs → Suffix xs zs
  suffix-trans {xs} (txy , exy) (tyz , eyz) =
    tyz ++ txy , ++-assoc tyz txy xs ∙ ap (tyz ++_) exy ∙ eyz

  suffix-∷ : Suffix xs (x ∷ xs)
  suffix-∷ {x} = x ∷ [] , refl

  suffix-uncons-r : x ≠ y → Suffix (x ∷ xs) (y ∷ ys) → Suffix (x ∷ xs) ys
  suffix-uncons-r x≠y ([]    , e) =
    absurd (x≠y (∷-head-inj e))
  suffix-uncons-r x≠y (z ∷ t , e) =
    t , ∷-tail-inj e

  suffix-split-r : x ∉ zs → Suffix (x ∷ xs) (zs ++ ys) → Suffix (x ∷ xs) ys
  suffix-split-r {zs = []}     x∉ sf = sf
  suffix-split-r {zs = z ∷ zs} x∉ sf =
    let (x≠z , x∉') = ¬any-uncons x∉ in
    suffix-split-r x∉' (suffix-uncons-r x≠z sf)

  suffix-uncons1 : Suffix (x ∷ xs) ys → Suffix1 xs ys
  suffix-uncons1 {x} {xs} (txy , exy) =
    x , txy , exy

  suffix-length : Suffix xs ys → length xs ≤ length ys
  suffix-length (txy , exy) = ≤-+-l ∙ =→≤ (++-length txy _ ⁻¹ ∙ ap length exy)

  suffix→ope : Suffix xs ys → OPE xs ys
  suffix→ope (txy , exy) = ope-++-l ∙ =→ope exy

  suffix1-weaken : Suffix1 xs ys → Suffix xs ys
  suffix1-weaken {xs} (t , txy , exy) =
    txy ∷r t , ap (_++ xs) (snoc-append txy) ∙ ++-assoc txy _ _ ∙ exy

  -- can't be placed in Data.List.Operations.Properties due to import cycles
  drop-suffix : {n : ℕ} {xs : List A}
              → Suffix (drop n xs) xs
  drop-suffix {n} {xs} = take n xs , split-take-drop n ⁻¹              
