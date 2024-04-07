{-# OPTIONS --safe #-}
module Algebra.Semigroup where

open import Categories.Prelude

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

opaque
  is-semigroup-is-prop : is-prop (is-semigroup _✦_)
  is-semigroup-is-prop S = ≅→is-of-hlevel! 1 is-semigroup-iso S where
    open is-semigroup S

instance opaque
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

semigroup-on↪magma-on : Semigroup-on A ↪ₜ Magma-on A
semigroup-on↪magma-on .fst S .n-Magma-on._⋆_ = S .Semigroup-on._⋆_
semigroup-on↪magma-on .fst S .n-Magma-on.has-n-magma =
  S .Semigroup-on.has-semigroup .is-semigroup.has-magma
semigroup-on↪magma-on .snd = set-injective→is-embedding! λ p →
  Equiv.injective (≅ₜ→≃ semigroup-on-iso) $ Σ-prop-pathᴾ! (ap n-Magma-on._⋆_ p)

instance opaque
  H-Level-semigroup-on : H-Level (2 + n) (Semigroup-on A)
  H-Level-semigroup-on = hlevel-basic-instance 2 $ ↪→is-of-hlevel! 2 semigroup-on↪magma-on


record make-semigroup {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    semigroup-is-set : is-set X
    _⋆_   : X → X → X
    assoc : Associative _⋆_

  to-is-semigroup : is-semigroup _⋆_
  to-is-semigroup .is-semigroup.has-magma .is-n-magma.has-is-of-hlevel = semigroup-is-set
  to-is-semigroup .is-semigroup.assoc = assoc

  to-semigroup-on : Semigroup-on X
  to-semigroup-on .Semigroup-on._⋆_ = _⋆_
  to-semigroup-on .Semigroup-on.has-semigroup = to-is-semigroup

open make-semigroup using (to-is-semigroup ; to-semigroup-on) public
