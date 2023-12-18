{-# OPTIONS --safe #-}
module Algebra.Rig where

open import Foundations.Base

open import Meta.Record
open import Meta.Search.HLevel
  hiding (_+_)
open import Meta.Variadic

open import Algebra.Semiring public

private variable
  ℓ     : Level
  A     : 𝒰 ℓ
  e x y z u : A
  _✦_ _✧_ : A → A → A
  n : HLevel

Absorb-left : (e : A) (_✧_ : A → A → A) → _
Absorb-left {A} e _✧_ = Π[ x ꞉ A ] (e ✧ x ＝ e)

Absorb-right : (e : A) (_✧_ : A → A → A) → _
Absorb-right {A} e _✧_ = Π[ x ꞉ A ] (x ✧ e ＝ e)

-- rigs (absorptive semirings)

record is-rig {A : 𝒰 ℓ}
    (0a : A) (1a : A)
    (_+_ : A → A → A)
    (_·_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-semiring : is-semiring 0a 1a _+_ _·_
  open is-semiring has-semiring public

  field
    ·-absorb-l : Absorb-left  0a _·_
    ·-absorb-r : Absorb-right 0a _·_

unquoteDecl is-rig-iso = declare-record-iso is-rig-iso (quote is-rig)

is-rig-is-prop : is-prop (is-rig e u _✦_ _✧_)
is-rig-is-prop = is-prop-η λ x → let open is-rig x in is-prop-β
  (is-of-hlevel-≃ 1 (iso→equiv is-rig-iso) hlevel!) x

instance
  H-Level-is-rig : H-Level (suc n) (is-rig e u _✦_ _✧_)
  H-Level-is-rig = hlevel-prop-instance is-rig-is-prop


record Rig-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    nil unit : X
    _+_ _·_ : X → X → X
    has-rig : is-rig nil unit _+_ _·_

  open is-rig has-rig public
  infixr 20 _+_
  infixr 30 _·_

unquoteDecl rig-on-iso = declare-record-iso rig-on-iso (quote Rig-on)


rig→semiring : ∀[ Rig-on {ℓ} →̇ Semiring-on {ℓ} ]
rig→semiring R .Semiring-on.nil = R .Rig-on.nil
rig→semiring R .Semiring-on.unit = R .Rig-on.unit
rig→semiring R .Semiring-on._+_ = R .Rig-on._+_
rig→semiring R .Semiring-on._·_ = R .Rig-on._·_
rig→semiring R .Semiring-on.has-semiring =
  R .Rig-on.has-rig .is-rig.has-semiring


record make-rig {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    rig-is-set : is-set X
    nil unit : X
    _+_ _·_ : X → X → X
    +-id-l  : Unital-left  nil _+_
    +-id-r  : Unital-right nil _+_
    +-assoc : Associative _+_
    +-comm  : Commutative _+_
    ·-id-l  : Unital-left  unit _·_
    ·-id-r  : Unital-right unit _·_
    ·-assoc : Associative _·_
    ·-distrib-+-l : Distrib-left  _·_ _+_
    ·-distrib-+-r : Distrib-right _·_ _+_
    ·-absorb-l : Absorb-left  nil _·_
    ·-absorb-r : Absorb-right nil _·_

  -- what an abomination
  to-rig-on : Rig-on X
  to-rig-on .Rig-on.nil = nil
  to-rig-on .Rig-on.unit = unit
  to-rig-on .Rig-on._+_ = _+_
  to-rig-on .Rig-on._·_ = _·_
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.+-comm-monoid
    .is-comm-monoid.has-monoid .is-monoid.has-semigroup
    .is-semigroup.has-magma .is-n-magma.has-is-of-hlevel = rig-is-set
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.+-comm-monoid
    .is-comm-monoid.has-monoid .is-monoid.has-semigroup .is-semigroup.assoc = +-assoc
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.+-comm-monoid
    .is-comm-monoid.has-monoid .is-monoid.id-l = +-id-l
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.+-comm-monoid
    .is-comm-monoid.has-monoid .is-monoid.id-r = +-id-r
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.+-comm-monoid
    .is-comm-monoid.comm = +-comm
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.·-monoid
    .is-monoid.has-semigroup .is-semigroup.has-magma
    .is-n-magma.has-is-of-hlevel = rig-is-set
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.·-monoid
    .is-monoid.has-semigroup .is-semigroup.assoc = ·-assoc
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.·-monoid
    .is-monoid.id-l = ·-id-l
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.·-monoid
    .is-monoid.id-r = ·-id-r
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.·-distrib-+-l =
    ·-distrib-+-l
  to-rig-on .Rig-on.has-rig .is-rig.has-semiring .is-semiring.·-distrib-+-r =
    ·-distrib-+-r
  to-rig-on .Rig-on.has-rig .is-rig.·-absorb-l = ·-absorb-l
  to-rig-on .Rig-on.has-rig .is-rig.·-absorb-r = ·-absorb-r

open make-rig using (to-rig-on) public
