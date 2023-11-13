{-# OPTIONS --safe #-}
module Algebra.Semiring where

open import Foundations.Base

open import Meta.Record
open import Meta.Search.HLevel
open import Meta.SIP

open import Algebra.Monoid.Commutative public

private variable
  ℓ     : Level
  A     : Type ℓ
  e x y z u : A
  _✦_ _✧_ : A → A → A
  n : HLevel

Distrib-left : (_*_ _+_ : A → A → A) → _
Distrib-left {A} _*_ _+_ = (x y z : A) → x * (y + z) ＝ (x * y) + (x * z)

Distrib-right : (_*_ _+_ : A → A → A) → _
Distrib-right {A} _*_ _+_ = (x y z : A) → (y + z) * x ＝ (y * x) + (z * x)

Raw-∞-semiring-on : Type ℓ → Type ℓ
Raw-∞-semiring-on X = X × (X → X → X) × X × (X → X → X)


-- semirings (nonabsorptive)

record is-semiring {A : Type ℓ}
    (0a : A) (_+_ : A → A → A)
    (1a : A) (_*_ : A → A → A) : Type ℓ where
  no-eta-equality
  field +-comm-monoid : is-comm-monoid 0a _+_
  open is-comm-monoid +-comm-monoid public
    renaming ( assoc to +-assoc
             ; id-l  to +-id-l
             ; id-r  to +-id-r
             ; comm  to +-comm )

  field *-monoid : is-monoid 1a _*_
  open is-monoid *-monoid hiding (has-is-of-hlevel ; H-Level-magma-carrier) public
    renaming ( assoc to *-assoc
             ; id-l  to *-id-l
             ; id-r  to *-id-r )

  field
    *-distrib-+-l : Distrib-left  _*_ _+_
    *-distrib-+-r : Distrib-right _*_ _+_

unquoteDecl is-semiring-iso = declare-record-iso is-semiring-iso (quote is-semiring)

is-semiring-is-prop : is-prop (is-semiring e _✦_ u _✧_)
is-semiring-is-prop = is-prop-η λ x → let open is-semiring x in is-prop-β
  (is-of-hlevel-≃ 1 (iso→equiv is-semiring-iso) hlevel!) x

instance
  H-Level-is-semiring : H-Level (suc n) (is-semiring e _✦_ u _✧_)
  H-Level-is-semiring = hlevel-prop-instance is-semiring-is-prop

Semiring-on : Type ℓ → Type ℓ
Semiring-on X =
  Σ[ (0a , _+_ , 1a , _*_) ꞉ X × (X → X → X) × X × (X → X → X) ] (is-semiring 0a _+_ 1a _*_)

private
  semiring-desc : Desc ℓ ℓ Raw-∞-semiring-on ℓ
  semiring-desc .Desc.descriptor = auto-str-term!
  semiring-desc .Desc.axioms _ = is-semiring $⁴_
  semiring-desc .Desc.axioms-prop _ _ = is-semiring-is-prop

semiring-str : Structure ℓ _
semiring-str = desc→structure semiring-desc

@0 semiring-str-is-univalent : is-univalent (semiring-str {ℓ})
semiring-str-is-univalent = desc→is-univalent semiring-desc

Semiring : (ℓ : Level) → Type (ℓsuc ℓ)
Semiring ℓ = Σ[ X ꞉ Type ℓ ] Semiring-on X
