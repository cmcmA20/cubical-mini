
module Algebra.Semiring where

open import Foundations.Base

open import Algebra.Monoid.Abelian
open import Algebra.Monoid

private variable
  ℓ     : Level
  A     : 𝒰 ℓ
  x y z : A

record is-semiring
  {ℓ}
  {R       : 𝒰 ℓ}
  (𝟏 𝟎     : R)
  (_*_ _+_ : R → R → R)
           : 𝒰 ℓ
    where
  field
    +-is-abelian-monoid : is-abelian-monoid 𝟎 _+_
    *-is-monoid         : is-monoid         𝟏 _*_

    *-distributes-over-+-right : x * (y + z) ＝ (x * y) + (x * z)
    *-distributes-over-+-left  : (y + z) * x ＝ (y * x) + (z * x)

    𝟎-absorbs-right : 𝟎 * x ＝ 𝟎
    𝟎-absorbs-left  : x * 𝟎 ＝ 𝟎

record Semiring-on {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  field
    𝟏 𝟎             : A
    _*_ _+_         : A → A → A
    has-is-semiring : is-semiring 𝟏 𝟎 _*_ _+_

  infixl 20 _+_
  infixl 30 _*_

  open is-semiring has-is-semiring public

Semiring : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
Semiring ℓ = Σ[ A ꞉ 𝒰 ℓ ] Semiring-on A

open import Meta.Underlying

-- instance
--   semiring-underlying : Underlying (Semiring ℓ)
--   semiring-underlying {ℓ} .Underlying.ℓ-underlying = ℓ
--   Underlying.⌞ semiring-underlying ⌟ = fst