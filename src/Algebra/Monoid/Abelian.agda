
module Algebra.Monoid.Abelian where

open import Foundations.Base

open import Algebra.Monoid

private variable
  ℓ : Level
  A : 𝒰 ℓ
  x y z : A

record is-abelian-monoid
  {ℓ}
  {G   : 𝒰 ℓ}
  (𝟏   : G)
  (_*_ : G → G → G)
       : 𝒰 ℓ
    where
  no-eta-equality
  field
    has-is-monoid : is-monoid 𝟏 _*_
    commutes      : x * y ＝ y * x

  open is-monoid has-is-monoid public

  field
    abel-coh : ∀{x y} →
      commutes {x = x} {y = y} ∙ commutes
        ＝
      refl

record Abelian-monoid-on (T : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    𝟏         : T
    _*_       : T → T → T
    has-is-ab : is-abelian-monoid 𝟏 _*_
  open is-abelian-monoid has-is-ab public

open import Meta.Marker

exchange :
  {𝟏   : A}
  {_*_ : A → A → A}
  (R   : is-abelian-monoid 𝟏 _*_)
       → ((x * y) * z) ＝ ((x * z) * y)
exchange {x} {y} {z} {𝟏} {_*_} R =
  (x *   y) * z    ＝⟨ sym (associative has-is-monoid _ _ _) ⟩
  (x * ⌜ y  * z ⌝) ＝⟨ ap! commutes ⟩
  (x *  (z  * y))  ＝⟨ associative has-is-monoid _ _ _ ⟩
  (x *   z) * y ∎
  where
    open is-abelian-monoid R
