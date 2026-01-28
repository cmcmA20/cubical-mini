{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.Pairwise where

open import Meta.Prelude
open import Meta.Extensionality
open import Meta.Effect

open import Data.Empty.Base as ⊥
open import Data.Unit.Base
open import Data.Reflects.Base
open import Data.List.Base
open import Data.List.Instances.Map
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Unary.At

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  P Q R : A → A → 𝒰 ℓ
  S : B → B → 𝒰 ℓ′
  @0 x0 : A
  @0 xs ys : List A

infixr 5 _∷ᵖ_
data Pairwise {ℓ ℓᵃ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) : @0 List A → 𝒰 (ℓ ⊔ ℓᵃ) where
  []ᵖ  : Pairwise R []
  _∷ᵖ_ : ∀ {x xs} → All (R x) xs → Pairwise R xs → Pairwise R (x ∷ xs)

-- TODO code

pairwise-++ : {xs ys : List A}
            → Pairwise R xs → Pairwise R ys
            → All (λ x → All (R x) ys) xs
            → Pairwise R (xs ++ ys)
pairwise-++  []ᵖ          pys []        = pys
pairwise-++ (arx ∷ᵖ pxs) pys (rx ∷ ax) =
  all-++ arx rx ∷ᵖ pairwise-++ pxs pys ax

pairwise-split : {xs ys : List A}
               → Pairwise R (xs ++ ys)
               → Pairwise R xs × Pairwise R ys × All (λ x → All (R x) ys) xs
pairwise-split {xs = []} prx = []ᵖ , prx , []
pairwise-split {xs = x ∷ xs} (axy ∷ᵖ prx) =
  let (ax , ay) = all-split {xs = xs} axy
      (px , py , ax') = pairwise-split {xs = xs} prx
    in
  ax ∷ᵖ px , py , ay ∷ ax'
