{-# OPTIONS --safe #-}
module Correspondences.Separated where

open import Foundations.Base

open import Meta.Search.HLevel

open import Structures.Base
open import Structures.IdentitySystem.Base

open import Correspondences.Base public
open import Correspondences.Classical

import Data.Empty.Base as ⊥
open import Data.Empty.Instances.HLevel

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

_separated_ : (S : Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S separated A = (S weakly-stable_) on-paths-of A

opaque
  unfolding Essentially-classical
  is-¬¬-separated : Type ℓ → Type ℓ
  is-¬¬-separated A = ¬¬_ separated A

  is-¬¬-separated-β : is-¬¬-separated A → Essentially-classical on-paths-of A
  is-¬¬-separated-β = id

  is-¬¬-separated-η : Essentially-classical on-paths-of A → is-¬¬-separated A
  is-¬¬-separated-η = id

¬¬-separated-identity-system
  : is-¬¬-separated A
  → is-identity-system (mapⁿ 2 ¬¬_ _＝_) (λ _ k → k refl)
¬¬-separated-identity-system A-sep =
  set-identity-system hlevel! $ essentially-classical-β $ is-¬¬-separated-β A-sep _ _

is-¬¬-separated→is-set : is-¬¬-separated A → is-set A
is-¬¬-separated→is-set As = identity-system→hlevel _ (¬¬-separated-identity-system As) hlevel!

opaque
  unfolding is-of-hlevel is-¬¬-separated
  is-¬¬-separated-is-prop : is-prop (is-¬¬-separated A)
  is-¬¬-separated-is-prop As As′ =
    fun-ext λ x i y p j → (is-¬¬-separated→is-set As) x y (As _ _ p) (As′ _ _ p) i j
