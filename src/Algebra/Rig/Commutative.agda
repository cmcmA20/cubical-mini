{-# OPTIONS --safe #-}
module Algebra.Rig.Commutative where

open import Categories.Prelude hiding (_+_)

open import Algebra.Rig public

private variable
  ℓ     : Level
  A     : 𝒰 ℓ
  e x y z u : A
  _✦_ _✧_ : A → A → A
  n : HLevel

-- commutative rigs

record is-comm-rig {A : 𝒰 ℓ}
    (_+_ : A → A → A)
    (_·_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-rig : is-rig _+_ _·_
  open is-rig has-rig public

  field ·-comm : Commutative _·_

unquoteDecl is-comm-rig-iso = declare-record-iso is-comm-rig-iso (quote is-comm-rig)

opaque
  is-comm-rig-is-prop : is-prop (is-comm-rig _✦_ _✧_)
  is-comm-rig-is-prop R = ≅→is-of-hlevel! 1 is-comm-rig-iso R where
    open is-comm-rig R

instance opaque
  H-Level-is-comm-rig : ⦃ n ≥ʰ 1 ⦄ → H-Level n (is-comm-rig _✦_ _✧_)
  H-Level-is-comm-rig ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-comm-rig-is-prop


record CRig-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _+_ _·_ : X → X → X
    has-comm-rig : is-comm-rig _+_ _·_

  open is-comm-rig has-comm-rig public
  infixr 20 _+_
  infixr 30 _·_

unquoteDecl crig-on-iso = declare-record-iso crig-on-iso (quote CRig-on)

comm-rig-on↪rig-on : CRig-on A ↪ₜ Rig-on A
comm-rig-on↪rig-on .fst R .Rig-on._+_ = R .CRig-on._+_
comm-rig-on↪rig-on .fst R .Rig-on._·_ = R .CRig-on._·_
comm-rig-on↪rig-on .fst R .Rig-on.has-rig =
  R .CRig-on.has-comm-rig .is-comm-rig.has-rig
comm-rig-on↪rig-on .snd = set-injective→is-embedding! λ p →
  Equiv.injective (≅ₜ→≃ crig-on-iso) $
    ap Rig-on._+_ p ,ₚ ap Rig-on._·_ p ,ₚ prop!

instance opaque
  H-Level-comm-rig-on : ⦃ n ≥ʰ 2 ⦄ → H-Level n (CRig-on A)
  H-Level-comm-rig-on ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $ ↪→is-of-hlevel! 2 comm-rig-on↪rig-on


record make-comm-rig {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    comm-rig-is-set : is-set X
    0a 1a : X
    _+_ _·_ : X → X → X
    +-id-l  : Unital-left  0a _+_
    +-id-r  : Unital-right 0a _+_
    +-assoc : Associative _+_
    +-comm  : Commutative _+_
    ·-id-l  : Unital-left  1a _·_
    ·-id-r  : Unital-right 1a _·_
    ·-assoc : Associative _·_
    ·-comm  : Commutative _·_
    ·-distrib-+-l : Distrib-left  _·_ _+_
    ·-distrib-+-r : Distrib-right _·_ _+_
    ·-absorb-l : Absorb-left  0a _·_
    ·-absorb-r : Absorb-right 0a _·_

  to-is-comm-rig : is-comm-rig _+_ _·_
  to-is-comm-rig .is-comm-rig.has-rig = to-is-rig go where
    go : make-rig X
    go .make-rig.rig-is-set = comm-rig-is-set
    go .make-rig.0a = 0a
    go .make-rig.1a = 1a
    go .make-rig._+_ = _+_
    go .make-rig._·_ = _·_
    go .make-rig.+-id-l = +-id-l
    go .make-rig.+-id-r = +-id-r
    go .make-rig.+-assoc = +-assoc
    go .make-rig.+-comm = +-comm
    go .make-rig.·-id-l = ·-id-l
    go .make-rig.·-id-r = ·-id-r
    go .make-rig.·-assoc = ·-assoc
    go .make-rig.·-distrib-+-l = ·-distrib-+-l
    go .make-rig.·-distrib-+-r = ·-distrib-+-r
    go .make-rig.·-absorb-l = ·-absorb-l
    go .make-rig.·-absorb-r = ·-absorb-r
  to-is-comm-rig .is-comm-rig.·-comm = ·-comm

  to-comm-rig-on : CRig-on X
  to-comm-rig-on .CRig-on._+_ = _+_
  to-comm-rig-on .CRig-on._·_ = _·_
  to-comm-rig-on .CRig-on.has-comm-rig = to-is-comm-rig

open make-comm-rig using (to-is-comm-rig ; to-comm-rig-on) public
