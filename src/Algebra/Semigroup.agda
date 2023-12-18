{-# OPTIONS --safe #-}
module Algebra.Semigroup where

open import Foundations.Base

open import Meta.Record
open import Meta.Search.HLevel
open import Meta.Variadic

open import Algebra.Magma public

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  _✦_ : A → A → A
  n : HLevel

Associative : (_⋆_ : A → A → A) → 𝒰 _
Associative {A} _⋆_ = (x y z : A) → x ⋆ (y ⋆ z) ＝ (x ⋆ y) ⋆ z

-- semigroups

record is-semigroup {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field
    has-magma : is-magma _⋆_
    assoc     : Associative _⋆_

  open is-n-magma has-magma public

unquoteDecl is-semigroup-iso = declare-record-iso is-semigroup-iso (quote is-semigroup)

is-semigroup-is-prop : is-prop (is-semigroup _✦_)
is-semigroup-is-prop = is-prop-η λ x → let open is-semigroup x in is-prop-β
  (iso→is-of-hlevel 1 is-semigroup-iso hlevel!) x

instance
  H-Level-is-semigroup : H-Level (suc n) (is-semigroup _✦_)
  H-Level-is-semigroup = hlevel-prop-instance is-semigroup-is-prop

record Semigroup-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _⋆_ : X → X → X
    has-semigroup : is-semigroup _⋆_

  open is-semigroup has-semigroup public
  infixr 20 _⋆_

unquoteDecl semigroup-on-iso = declare-record-iso semigroup-on-iso (quote Semigroup-on)

semigroup→magma : ∀[ Semigroup-on {ℓ} →̇ Magma-on {ℓ} ]
semigroup→magma sg .n-Magma-on._⋆_ = sg .Semigroup-on._⋆_
semigroup→magma sg .n-Magma-on.has-n-magma = sg .Semigroup-on.has-semigroup .is-semigroup.has-magma


record make-semigroup {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    semigroup-is-set : is-set X
    _⋆_   : X → X → X
    assoc : Associative _⋆_

  to-semigroup-on : Semigroup-on X
  to-semigroup-on .Semigroup-on._⋆_ = _⋆_
  to-semigroup-on .Semigroup-on.has-semigroup .is-semigroup.has-magma .is-n-magma.has-is-of-hlevel =
    semigroup-is-set
  to-semigroup-on .Semigroup-on.has-semigroup .is-semigroup.assoc = assoc

open make-semigroup using (to-semigroup-on) public
