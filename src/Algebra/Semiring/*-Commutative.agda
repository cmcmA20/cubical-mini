
module Algebra.Semiring.*-Commutative where

open import Foundations.Base

open import Algebra.Monoid.Abelian
open import Algebra.Monoid
open import Algebra.Semiring

private variable
  ℓ     : Level
  A     : 𝒰 ℓ
  x y z : A

record is-commutative-semiring
  {ℓ}
  {R       : 𝒰 ℓ}
  (𝟏 𝟎     : R)
  (_*_ _+_ : R → R → R)
           : 𝒰 ℓ
    where
  field
    has-is-semiring     : is-semiring 𝟏 𝟎 _*_ _+_
    *-is-abelian-monoid : is-abelian-monoid 𝟏 _*_

  open is-semiring has-is-semiring public

record CommutativeSemiring-on {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  field
    𝟏 𝟎             : A
    _*_ _+_         : A → A → A
    has-is-commutative-semiring : is-commutative-semiring 𝟏 𝟎 _*_ _+_

  infixl 20 _+_
  infixl 30 _*_

  open is-commutative-semiring has-is-commutative-semiring public

CommutativeSemiring : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
CommutativeSemiring ℓ = Σ[ A ꞉ 𝒰 ℓ ] CommutativeSemiring-on A

open import Meta.Underlying

-- instance
--   semiring-underlying : Underlying (Semiring ℓ)
--   semiring-underlying {ℓ} .Underlying.ℓ-underlying = ℓ
--   Underlying.⌞ semiring-underlying ⌟ = fst