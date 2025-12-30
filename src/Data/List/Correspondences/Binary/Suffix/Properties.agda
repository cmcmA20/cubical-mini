{-# OPTIONS --safe #-}
module Data.List.Correspondences.Binary.Suffix.Properties where

open import Meta.Prelude
open import Meta.Effect
open import Meta.Extensionality
open Variadics _

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Dec as Dec
open import Data.Empty.Base
open import Data.Empty.Properties as ⊥
open import Data.List
open import Data.List.Operations.Properties
open import Data.List.Instances.Map

open import Data.List.Correspondences.Binary.Prefix
open import Data.List.Correspondences.Binary.Suffix

-- TODO mostly interaction between prefix and suffix

private variable
  ℓᵃ ℓᵇ ℓ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

opaque
  unfolding Prefix Suffix

  suffix-map : {f : A → B} {xs ys : List A}
             → Suffix xs ys
             → Suffix (mapₗ f xs) (mapₗ f ys)
  suffix-map {f} (txy , exy) =
    map f txy , map-++ f txy _ ⁻¹ ∙ ap (map f) exy

  suffix→reverse-prefix : {xs ys : List A}
                        → Suffix xs ys
                        → Prefix (reverse xs) (reverse ys)
  suffix→reverse-prefix (ts , e) =
    reverse ts , reverse-++ {xs = ts} ⁻¹ ∙ ap reverse e

opaque
  unfolding Prefix1 Suffix1
  suffix1→reverse-prefix1 : {xs ys : List A}
                          → Suffix1 xs ys
                          → Prefix1 (reverse xs) (reverse ys)
  suffix1→reverse-prefix1 {xs} (t , ts , e) =
      t , reverse ts
    ,   ++-assoc (reverse xs) (t ∷ []) (reverse ts) ⁻¹
      ∙ reverse-++ {xs = ts} ⁻¹
      ∙ ap reverse e

  suffix1-map : {f : A → B} {xs ys : List A}
             → Suffix1 xs ys
             → Suffix1 (mapₗ f xs) (mapₗ f ys)
  suffix1-map {f} (t , txy , exy) =
      f t , map f txy
    , map-++ f txy _ ⁻¹ ∙ ap (map f) exy
