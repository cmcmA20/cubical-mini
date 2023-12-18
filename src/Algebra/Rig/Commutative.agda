{-# OPTIONS --safe #-}
module Algebra.Rig.Commutative where

open import Foundations.Base

open import Meta.Record
open import Meta.Search.HLevel
  hiding (_+_)
open import Meta.Variadic

open import Algebra.Rig public

private variable
  ℓ     : Level
  A     : 𝒰 ℓ
  e x y z u : A
  _✦_ _✧_ : A → A → A
  n : HLevel

-- commutative rigs

record is-comm-rig {A : 𝒰 ℓ}
    (0a : A) (1a : A)
    (_+_ : A → A → A)
    (_·_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-rig : is-rig 0a 1a _+_ _·_
  open is-rig has-rig public

  field ·-comm : Commutative _·_

unquoteDecl is-comm-rig-iso = declare-record-iso is-comm-rig-iso (quote is-comm-rig)

is-comm-rig-is-prop : is-prop (is-comm-rig e u _✦_ _✧_)
is-comm-rig-is-prop = is-prop-η λ x → let open is-comm-rig x in is-prop-β
  (is-of-hlevel-≃ 1 (iso→equiv is-comm-rig-iso) hlevel!) x

instance
  H-Level-is-comm-rig : H-Level (suc n) (is-comm-rig e u _✦_ _✧_)
  H-Level-is-comm-rig = hlevel-prop-instance is-comm-rig-is-prop


record CRig-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    nil unit : X
    _+_ _·_ : X → X → X
    has-comm-rig : is-comm-rig nil unit _+_ _·_

  open is-comm-rig has-comm-rig public
  infixr 20 _+_
  infixr 30 _·_

unquoteDecl crig-on-iso = declare-record-iso crig-on-iso (quote CRig-on)

comm-rig→rig : ∀[ CRig-on {ℓ} →̇ Rig-on {ℓ} ]
comm-rig→rig R .Rig-on.nil = R .CRig-on.nil
comm-rig→rig R .Rig-on.unit = R .CRig-on.unit
comm-rig→rig R .Rig-on._+_ = R .CRig-on._+_
comm-rig→rig R .Rig-on._·_ = R .CRig-on._·_
comm-rig→rig R .Rig-on.has-rig =
  R .CRig-on.has-comm-rig .is-comm-rig.has-rig

record make-comm-rig {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    comm-rig-is-set : is-set X
    nil unit : X
    _+_ _·_ : X → X → X
    +-id-l  : Unital-left  nil _+_
    +-id-r  : Unital-right nil _+_
    +-assoc : Associative _+_
    +-comm  : Commutative _+_
    ·-id-l  : Unital-left  unit _·_
    ·-id-r  : Unital-right unit _·_
    ·-assoc : Associative _·_
    ·-comm  : Commutative _·_
    ·-distrib-+-l : Distrib-left  _·_ _+_
    ·-distrib-+-r : Distrib-right _·_ _+_
    ·-absorb-l : Absorb-left  nil _·_
    ·-absorb-r : Absorb-right nil _·_

  to-comm-rig-on : CRig-on X
  to-comm-rig-on .CRig-on.nil = nil
  to-comm-rig-on .CRig-on.unit = unit
  to-comm-rig-on .CRig-on._+_ = _+_
  to-comm-rig-on .CRig-on._·_ = _·_
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.+-comm-monoid .is-comm-monoid.has-monoid
    .is-monoid.has-semigroup .is-semigroup.has-magma
    .is-n-magma.has-is-of-hlevel = comm-rig-is-set
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.+-comm-monoid .is-comm-monoid.has-monoid
    .is-monoid.has-semigroup .is-semigroup.assoc = +-assoc
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.+-comm-monoid .is-comm-monoid.has-monoid .is-monoid.id-l = +-id-l
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.+-comm-monoid .is-comm-monoid.has-monoid .is-monoid.id-r = +-id-r
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.+-comm-monoid .is-comm-monoid.comm = +-comm
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.·-monoid .is-monoid.has-semigroup
    .is-semigroup.has-magma .is-n-magma.has-is-of-hlevel = comm-rig-is-set
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.·-monoid .is-monoid.has-semigroup .is-semigroup.assoc = ·-assoc
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.·-monoid .is-monoid.id-l = ·-id-l
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.·-monoid .is-monoid.id-r = ·-id-r
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.·-distrib-+-l = ·-distrib-+-l
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.has-semiring
    .is-semiring.·-distrib-+-r = ·-distrib-+-r
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.·-absorb-l =
    ·-absorb-l
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.has-rig .is-rig.·-absorb-r =
    ·-absorb-r
  to-comm-rig-on .CRig-on.has-comm-rig .is-comm-rig.·-comm = ·-comm

open make-comm-rig using (to-comm-rig-on) public
