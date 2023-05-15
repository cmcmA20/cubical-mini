{-# OPTIONS --safe #-}
module Structures.Pointed where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Univalence

private variable
  ℓ : Level
  A : Type ℓ

Pointed-str : Structure ℓ id
Pointed-str .is-hom (A , x) (B , y) f = f .fst x ＝ y

@0 Pointed-str-is-univalent : is-univalent (Pointed-str {ℓ})
Pointed-str-is-univalent f = ua-PathP≃path _

Id-action-is-transport : is-transport-str {ℓ} {ℓ} id
Id-action-is-transport f s = sym (transport-refl _)
