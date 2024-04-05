{-# OPTIONS --safe #-}
module Algebra.Rig where

open import Categories.Prelude hiding (_+_)

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
    (_+_ : A → A → A)
    (_·_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-semiring : is-semiring _+_ _·_
  open is-semiring has-semiring public

  field
    ·-absorb-l : Absorb-left  0a _·_
    ·-absorb-r : Absorb-right 0a _·_

unquoteDecl is-rig-iso = declare-record-iso is-rig-iso (quote is-rig)

opaque
  unfolding is-of-hlevel
  is-rig-is-prop : is-prop (is-rig _✦_ _✧_)
  is-rig-is-prop R = ≅→is-of-hlevel 1 is-rig-iso hlevel! R where
    open is-rig R

instance
  H-Level-is-rig : H-Level (suc n) (is-rig _✦_ _✧_)
  H-Level-is-rig = hlevel-prop-instance is-rig-is-prop


record Rig-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _+_ _·_ : X → X → X
    has-rig : is-rig _+_ _·_

  open is-rig has-rig public
  infixr 20 _+_
  infixr 30 _·_

unquoteDecl rig-on-iso = declare-record-iso rig-on-iso (quote Rig-on)


rig-on↪semiring-on : Rig-on A ↪ₜ Semiring-on A
rig-on↪semiring-on .fst R .Semiring-on._+_ = R .Rig-on._+_
rig-on↪semiring-on .fst R .Semiring-on._·_ = R .Rig-on._·_
rig-on↪semiring-on .fst R .Semiring-on.has-semiring =
  R .Rig-on.has-rig .is-rig.has-semiring
rig-on↪semiring-on .snd = set-injective→is-embedding hlevel! λ p →
  Equiv.injective (≅ₜ→≃ rig-on-iso) $
    ap Semiring-on._+_ p ,ₚ ap Semiring-on._·_ p ,ₚ prop!

rig-on-is-set : is-set (Rig-on A)
rig-on-is-set = is-embedding→is-of-hlevel 1 (rig-on↪semiring-on .snd) hlevel!

instance
  H-Level-rig-on : H-Level (suc (suc n)) (Rig-on A)
  H-Level-rig-on = hlevel-basic-instance 2 rig-on-is-set


record make-rig {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    rig-is-set : is-set X
    0a 1a : X
    _+_ _·_ : X → X → X
    +-id-l  : Unital-left  0a _+_
    +-id-r  : Unital-right 0a _+_
    +-assoc : Associative _+_
    +-comm  : Commutative _+_
    ·-id-l  : Unital-left  1a _·_
    ·-id-r  : Unital-right 1a _·_
    ·-assoc : Associative _·_
    ·-distrib-+-l : Distrib-left  _·_ _+_
    ·-distrib-+-r : Distrib-right _·_ _+_
    ·-absorb-l : Absorb-left  0a _·_
    ·-absorb-r : Absorb-right 0a _·_

  to-is-rig : is-rig _+_ _·_
  to-is-rig .is-rig.has-semiring = to-is-semiring go where
    go : make-semiring X
    go .make-semiring.semiring-is-set = rig-is-set
    go .make-semiring._+_ = _+_
    go .make-semiring._·_ = _·_
    go .make-semiring.0a = 0a
    go .make-semiring.+-id-l = +-id-l
    go .make-semiring.+-id-r = +-id-r
    go .make-semiring.+-assoc = +-assoc
    go .make-semiring.+-comm = +-comm
    go .make-semiring.1a = 1a
    go .make-semiring.·-id-l = ·-id-l
    go .make-semiring.·-id-r = ·-id-r
    go .make-semiring.·-assoc = ·-assoc
    go .make-semiring.·-distrib-+-l = ·-distrib-+-l
    go .make-semiring.·-distrib-+-r = ·-distrib-+-r
  to-is-rig .is-rig.·-absorb-l = ·-absorb-l
  to-is-rig .is-rig.·-absorb-r = ·-absorb-r

  to-rig-on : Rig-on X
  to-rig-on .Rig-on._+_ = _+_
  to-rig-on .Rig-on._·_ = _·_
  to-rig-on .Rig-on.has-rig = to-is-rig

open make-rig using (to-is-rig ; to-rig-on) public
