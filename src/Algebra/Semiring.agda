{-# OPTIONS --safe #-}
module Algebra.Semiring where

open import Categories.Prelude hiding (_+_)

open import Algebra.Monoid.Commutative public

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  e x y z u : A
  _✦_ _✧_ : A → A → A
  n : HLevel

Distrib-left : (_·_ _+_ : A → A → A) → _
Distrib-left {A} _·_ _+_ = (x y z : A) → x · (y + z) ＝ (x · y) + (x · z)

Distrib-right : (_·_ _+_ : A → A → A) → _
Distrib-right {A} _·_ _+_ = (x y z : A) → (y + z) · x ＝ (y · x) + (z · x)

-- semirings (nonabsorptive)

record is-semiring {A : 𝒰 ℓ}
    (0a : A) (1a : A)
    (_+_ : A → A → A)
    (_·_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field +-comm-monoid : is-comm-monoid 0a _+_
  open is-comm-monoid +-comm-monoid public
    renaming ( assoc to +-assoc
             ; id-l  to +-id-l
             ; id-r  to +-id-r
             ; comm  to +-comm )

  field ·-monoid : is-monoid 1a _·_
  open is-monoid ·-monoid hiding (has-is-of-hlevel ; H-Level-magma-carrier) public
    renaming ( assoc to ·-assoc
             ; id-l  to ·-id-l
             ; id-r  to ·-id-r )

  field
    ·-distrib-+-l : Distrib-left  _·_ _+_
    ·-distrib-+-r : Distrib-right _·_ _+_

unquoteDecl is-semiring-iso = declare-record-iso is-semiring-iso (quote is-semiring)

opaque
  unfolding is-of-hlevel
  is-semiring-is-prop : is-prop (is-semiring e u _✦_ _✧_)
  is-semiring-is-prop S = iso→is-of-hlevel 1 is-semiring-iso hlevel! S where
    open is-semiring S

instance
  H-Level-is-semiring : H-Level (suc n) (is-semiring e u _✦_ _✧_)
  H-Level-is-semiring = hlevel-prop-instance is-semiring-is-prop


record Semiring-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    nil unit : X
    _+_ _·_ : X → X → X
    has-semiring : is-semiring nil unit _+_ _·_

  open is-semiring has-semiring public
  infixr 20 _+_
  infixr 30 _·_

unquoteDecl semiring-on-iso = declare-record-iso semiring-on-iso (quote Semiring-on)

semiring-on-is-set : is-set (Semiring-on A)
semiring-on-is-set = iso→is-of-hlevel _ semiring-on-iso $ is-set-η λ (_ , _ , _ , _ , x) _ _ _ →
  let open is-semiring x in prop!


record Semiring-hom
  {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
  (M : Semiring-on A) (M′ : Semiring-on B) (e : A → B) : 𝒰 (ℓ ⊔ ℓ′)
  where
    private
      module A = Semiring-on M
      module B = Semiring-on M′

    field
      pres-0 : e A.nil ＝ B.nil
      pres-1 : e A.unit ＝ B.unit
      pres-+  : (x y : A) → e (x A.+ y) ＝ e x B.+ e y
      pres-·  : (x y : A) → e (x A.· y) ＝ e x B.· e y

unquoteDecl semiring-hom-iso = declare-record-iso semiring-hom-iso (quote Semiring-hom)

semiring-hom-is-prop : ∀ {M : Semiring-on A} {M′ : Semiring-on B} {f}
                     → is-prop (Semiring-hom M M′ f)
semiring-hom-is-prop {M′} = iso→is-of-hlevel _ semiring-hom-iso hlevel! where
  open Semiring-on M′

instance
  H-Level-semiring-on : H-Level (suc (suc n)) (Semiring-on A)
  H-Level-semiring-on = hlevel-basic-instance 2 semiring-on-is-set

  H-Level-semiring-hom : ∀ {M : Semiring-on A} {M′ : Semiring-on B} {f}
                       → H-Level (suc n) (Semiring-hom M M′ f)
  H-Level-semiring-hom = hlevel-prop-instance semiring-hom-is-prop


record make-semiring {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    semiring-is-set : is-set X
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

  to-is-semiring : is-semiring nil unit _+_ _·_
  to-is-semiring .is-semiring.+-comm-monoid = to-is-comm-monoid go where
    go : make-comm-monoid X
    go .make-comm-monoid.monoid-is-set = semiring-is-set
    go .make-comm-monoid.id = nil
    go .make-comm-monoid._⋆_ = _+_
    go .make-comm-monoid.id-l = +-id-l
    go .make-comm-monoid.id-r = +-id-r
    go .make-comm-monoid.assoc = +-assoc
    go .make-comm-monoid.comm = +-comm
  to-is-semiring .is-semiring.·-monoid = to-is-monoid go where
    go : make-monoid X
    go .make-monoid.monoid-is-set = semiring-is-set
    go .make-monoid.id = unit
    go .make-monoid._⋆_ = _·_
    go .make-monoid.id-l = ·-id-l
    go .make-monoid.id-r = ·-id-r
    go .make-monoid.assoc = ·-assoc
  to-is-semiring .is-semiring.·-distrib-+-l = ·-distrib-+-l
  to-is-semiring .is-semiring.·-distrib-+-r = ·-distrib-+-r

  to-semiring-on : Semiring-on X
  to-semiring-on .Semiring-on.nil = nil
  to-semiring-on .Semiring-on.unit = unit
  to-semiring-on .Semiring-on._+_ = _+_
  to-semiring-on .Semiring-on._·_ = _·_
  to-semiring-on .Semiring-on.has-semiring = to-is-semiring

open make-semiring using (to-is-semiring ; to-semiring-on) public
