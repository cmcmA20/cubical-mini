
module Algebra.Group.Abelian where

open import Foundations.Base

open import Algebra.Group

private variable
  ℓ : Level
  A : 𝒰 ℓ

record is-abelian-group {ℓ} {G : 𝒰 ℓ} (_*_ : G → G → G) : 𝒰 ℓ where
  no-eta-equality
  field
    has-is-group : is-group _*_
    commutes     : ∀ {x y} → x * y ＝ y * x

  open is-group has-is-group public

  field
    abel-coh : ∀{x y} →
      commutes {x = x} {y = y} ∙ commutes
        ＝
      refl

record Abelian-group-on (T : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _*_       : T → T → T
    has-is-ab : is-abelian-group _*_
  open is-abelian-group has-is-ab public
