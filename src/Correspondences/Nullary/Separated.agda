{-# OPTIONS --safe #-}
module Correspondences.Nullary.Separated where

open import Foundations.Base

open import Meta.Search.HLevel

open import Structures.Base
open import Structures.IdentitySystem.Base

open import Correspondences.Nullary.Classical

import Data.Empty.Base as ⊥
open import Data.Dec.Base

private variable
  ℓ : Level
  A : Type ℓ

opaque
  is-separated-at-hlevel : HLevel → Type ℓ → Type ℓ
  is-separated-at-hlevel 0 = ¬¬_ stable_
  is-separated-at-hlevel (suc n) = is-separated-at-hlevel n on-paths-of_

dec→¬¬-stable : Dec A → ¬¬_ stable A
dec→¬¬-stable (no ¬a) f = ⊥.rec (f ¬a)
dec→¬¬-stable (yes a) _ = a

is-separated : Type ℓ → Type ℓ
is-separated = is-separated-at-hlevel 1


opaque
  unfolding is-separated-at-hlevel
  separated-identity-system
    : is-separated A
    → is-identity-system (λ x y → ¬¬ (x ＝ y)) (λ _ k → k refl)
  separated-identity-system A-sep =
    set-identity-system (λ _ _ → hlevel!) (A-sep _ _)

opaque
  unfolding is-of-hlevel is-separated-at-hlevel
  is-separated→is-set
    : is-separated A
    → is-set A
  is-separated→is-set As =
    identity-system→hlevel 1
      (separated-identity-system As) λ _ _ _ f →
        fun-ext λ g → ⊥.rec (f g)

  is-separated-is-prop : is-prop (is-separated A)
  is-separated-is-prop As As′ =
    fun-ext λ x i y p j → (is-separated→is-set As) x y (As _ _ p) (As′ _ _ p) i j
