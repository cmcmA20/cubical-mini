{-# OPTIONS --safe #-}
module Data.List.Correspondences.Binary.Suffix where

open import Meta.Prelude

open import Data.Empty.Base
open import Data.Empty.Properties as ⊥
open import Data.List.Base
open import Data.List.Properties
open import Data.List.Operations
open import Data.List.Operations.Properties
open import Data.List.Correspondences.Binary.OPE
open import Data.Nat.Order.Base
open import Data.Acc.Base

private variable
  ℓᵃ ℓ : Level
  A : Type ℓᵃ
  x y : A
  xs ys zs ts : List A

opaque
  Suffix Suffix1 : Corr _ (List A , List A) (level-of-type A)

  Suffix {A} xs ys = Σ[ ts ꞉ List A ] (ts ++ xs ＝ ys)
  Suffix1 {A} xs ys = Σ[ t ꞉ A ] Σ[ ts ꞉ List A ] (t ∷ ts ++ xs ＝ ys)

-- TODO add more

opaque
  unfolding Suffix

  []-suffix : Suffix [] ys
  []-suffix {ys} = ys , ++-id-r ys

  suffix-refl : Suffix xs xs
  suffix-refl {xs} = [] , refl

  suffix-trans : Suffix xs ys → Suffix ys zs → Suffix xs zs
  suffix-trans {xs} (txy , exy) (tyz , eyz) =
    tyz ++ txy , ++-assoc tyz txy xs ∙ ap (tyz ++_) exy ∙ eyz

  suffix-∷ : Suffix xs (x ∷ xs)
  suffix-∷ {x} = x ∷ [] , refl

  suffix-uncons : Suffix (x ∷ xs) ys → Suffix xs ys
  suffix-uncons {x} {xs} (txy , exy) =
    txy ∷r x , ap (_++ xs) (snoc-append txy) ∙ ++-assoc txy _ _ ∙ exy

  suffix-length : Suffix xs ys → length xs ≤ length ys
  suffix-length (txy , exy) = ≤-+-l ∙ =→≤ (++-length txy _ ⁻¹ ∙ ap length exy)

  suffix→ope : Suffix xs ys → OPE xs ys
  suffix→ope (txy , exy) = ope-++-l ∙ =→ope exy
