{-# OPTIONS --safe #-}
module Algebra.Monoid.Commutative where

open import Foundations.Base hiding (id)

open import Meta.Marker
open import Meta.Record
open import Meta.Search.HLevel
open import Meta.Variadic

open import Algebra.Monoid public

private variable
  ℓ : Level
  A : 𝒰 ℓ
  e x y z : A
  _✦_ : A → A → A
  n : HLevel

Commutative : (_⋆_ : A → A → A) → 𝒰 _
Commutative {A} _⋆_ = Π[ x ꞉ A ] Π[ y ꞉ A ] (y ⋆ x ＝ x ⋆ y)

-- commutative monoids

record is-comm-monoid {A : 𝒰 ℓ} (id : A) (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-monoid : is-monoid id _⋆_
  open is-monoid has-monoid public

  field comm : Commutative _⋆_

unquoteDecl is-comm-monoid-iso = declare-record-iso is-comm-monoid-iso (quote is-comm-monoid)

is-comm-monoid-is-prop : is-prop (is-comm-monoid e _✦_)
is-comm-monoid-is-prop = is-prop-η λ x → let open is-comm-monoid x in is-prop-β
  (is-of-hlevel-≃ 1 (iso→equiv is-comm-monoid-iso) hlevel!) x

instance
  H-Level-is-comm-monoid : H-Level (suc n) (is-comm-monoid e _✦_)
  H-Level-is-comm-monoid = hlevel-prop-instance is-comm-monoid-is-prop

record CMonoid-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    id  : X
    _⋆_ : X → X → X
    has-comm-monoid : is-comm-monoid id _⋆_

  open is-comm-monoid has-comm-monoid public
  infixr 20 _⋆_

unquoteDecl cmonoid-on-iso = declare-record-iso cmonoid-on-iso (quote CMonoid-on)


comm-monoid→monoid : ∀[ CMonoid-on {ℓ} →̇ Monoid-on {ℓ} ]
comm-monoid→monoid M .Monoid-on.id = M .CMonoid-on.id
comm-monoid→monoid M .Monoid-on._⋆_ = M .CMonoid-on._⋆_
comm-monoid→monoid M .Monoid-on.has-monoid =
  M .CMonoid-on.has-comm-monoid .is-comm-monoid.has-monoid


record make-comm-monoid {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    monoid-is-set : is-set X
    id  : X
    _⋆_ : X → X → X
    id-l : Unital-left  id _⋆_
    id-r : Unital-right id _⋆_
    assoc : Associative _⋆_
    comm  : Commutative _⋆_

  to-comm-monoid-on : CMonoid-on X
  to-comm-monoid-on .CMonoid-on.id = id
  to-comm-monoid-on .CMonoid-on._⋆_ = _⋆_
  to-comm-monoid-on .CMonoid-on.has-comm-monoid .is-comm-monoid.has-monoid
    .is-monoid.has-semigroup .is-semigroup.has-magma
    .is-n-magma.has-is-of-hlevel = monoid-is-set
  to-comm-monoid-on .CMonoid-on.has-comm-monoid .is-comm-monoid.has-monoid
    .is-monoid.has-semigroup .is-semigroup.assoc = assoc
  to-comm-monoid-on .CMonoid-on.has-comm-monoid .is-comm-monoid.has-monoid
    .is-monoid.id-l = id-l
  to-comm-monoid-on .CMonoid-on.has-comm-monoid .is-comm-monoid.has-monoid
    .is-monoid.id-r = id-r
  to-comm-monoid-on .CMonoid-on.has-comm-monoid .is-comm-monoid.comm = comm

open make-comm-monoid using (to-comm-monoid-on) public


-- abelian monoid theory

module _ {M : CMonoid-on A} where
  open CMonoid-on M

  exchange : (x ⋆ y) ⋆ z ＝ (x ⋆ z) ⋆ y
  exchange {x} {y} {z} =
    (x ⋆ y) ⋆ z     ＝˘⟨ assoc _ _ _ ⟩
    x ⋆ ⌜ y  ⋆ z ⌝  ＝⟨ ap! (comm _ _) ⟩
    x ⋆ (z  ⋆ y)    ＝⟨ assoc _ _ _ ⟩
    (x ⋆ z) ⋆ y     ∎
