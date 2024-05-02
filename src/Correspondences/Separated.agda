{-# OPTIONS --safe #-}
module Correspondences.Separated where

open import Meta.Prelude

open import Correspondences.Classical

import Data.Empty.Base as ⊥

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

_separated_ : (S : Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S separated A = (S weakly-stable_) on-paths-of A

is-¬¬-separated : Type ℓ → Type ℓ
is-¬¬-separated A = ¬¬_ separated A

¬¬-separated-identity-system
  : is-¬¬-separated A
  → is-identity-system (mapⁿ 2 ¬¬_ _＝_) (λ _ k → k refl)
¬¬-separated-identity-system A-sep =
  set-identity-system! $ A-sep _ _

is-¬¬-separated→is-set : is-¬¬-separated A → is-set A
is-¬¬-separated→is-set As =
  identity-system→is-of-hlevel! 1 (¬¬-separated-identity-system As)

opaque
  is-¬¬-separated-is-prop : is-prop (is-¬¬-separated A)
  is-¬¬-separated-is-prop As As′ =
    fun-ext λ x i y p j → (is-¬¬-separated→is-set As) x y (As _ _ p) (As′ _ _ p) i j
