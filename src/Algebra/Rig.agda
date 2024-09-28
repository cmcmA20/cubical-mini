{-# OPTIONS --safe #-}
module Algebra.Rig where

open import Cat.Prelude hiding (_+_)

open import Algebra.Semiring public

private variable
  ℓ ℓ′  : Level
  A     : 𝒰 ℓ
  e x y z u : A
  _✦_ _✧_ : A → A → A
  n : HLevel

Absorb-l : (e : A) (_✧_ : A → A → A) (x : A) → _
Absorb-l {A} e _✧_ x = e ✧ x ＝ e

Absorb-r : (e : A) (_✧_ : A → A → A) (x : A) → _
Absorb-r {A} e _✧_ x = x ✧ e ＝ e

-- rigs (absorptive semirings)

record is-rig {A : 𝒰 ℓ}
    (_+_ : A → A → A)
    (_·_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-semiring : is-semiring _+_ _·_
  open is-semiring has-semiring public

  field
    ·-absorb-l : Π[ Absorb-l 0a _·_ ]
    ·-absorb-r : Π[ Absorb-r 0a _·_ ]

unquoteDecl is-rig-iso = declare-record-iso is-rig-iso (quote is-rig)

opaque
  is-rig-is-prop : is-prop (is-rig _✦_ _✧_)
  is-rig-is-prop R = ≅→is-of-hlevel! 1 is-rig-iso R where
    open is-rig R

instance opaque
  H-Level-is-rig : ⦃ n ≥ʰ 1 ⦄ → H-Level n (is-rig _✦_ _✧_)
  H-Level-is-rig ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-rig-is-prop


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
rig-on↪semiring-on .snd = set-injective→is-embedding! λ p →
  Equiv.injective (≅ₜ→≃ rig-on-iso) $
    ap Semiring-on._+_ p ,ₚ ap Semiring-on._·_ p ,ₚ prop!

instance opaque
  H-Level-rig-on : ⦃ n ≥ʰ 2 ⦄ → H-Level n (Rig-on A)
  H-Level-rig-on ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $ ↪→is-of-hlevel! 2 rig-on↪semiring-on

instance
  ⇒-Rig : ⇒-notation (Σ[ X ꞉ Set ℓ ] Rig-on ⌞ X ⌟) (Σ[ Y ꞉ Set ℓ′ ] Rig-on ⌞ Y ⌟) (𝒰 (ℓ ⊔ ℓ′))
  ⇒-Rig .⇒-notation.Constraint _ _ = ⊤
  ⇒-Rig ._⇒_ (A , X) (B , Y) = Total-hom (λ P Q → ⌞ P ⌟ → ⌞ Q ⌟)
    (λ f P Q → Semiring-hom f (rig-on↪semiring-on .fst P) (rig-on↪semiring-on .fst Q)) {a = A} {b = B} X Y


record make-rig {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    rig-is-set : is-set X
    0a 1a : X
    _+_ _·_ : X → X → X
    +-id-l  : Π[ Unitality-l X  0a _+_ ]
    +-id-r  : Π[ Unitality-r X 0a _+_ ]
    +-assoc : Π[ Associativity X _+_ ]
    +-comm  : Π[ Commutativity X _+_ ]
    ·-id-l  : Π[ Unitality-l X 1a _·_ ]
    ·-id-r  : Π[ Unitality-r X 1a _·_ ]
    ·-assoc : Π[ Associativity X _·_ ]
    ·-distrib-+-l : Π[ Distrib-l _·_ _+_ ]
    ·-distrib-+-r : Π[ Distrib-r _·_ _+_ ]
    ·-absorb-l : Π[ Absorb-l 0a _·_ ]
    ·-absorb-r : Π[ Absorb-r 0a _·_ ]

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
