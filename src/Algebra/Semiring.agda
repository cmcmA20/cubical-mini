{-# OPTIONS --safe #-}
module Algebra.Semiring where

open import Cat.Prelude hiding (_+_)

open import Algebra.Monoid.Commutative public

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  e x y z u : A
  _✦_ _✧_ : A → A → A
  n : HLevel

Distrib-l : (_·_ _+_ : A → A → A) (x y z : A) → _
Distrib-l {A} _·_ _+_ x y z = x · (y + z) ＝ (x · y) + (x · z)

Distrib-r : (_·_ _+_ : A → A → A) (x y z : A) → _
Distrib-r {A} _·_ _+_ x y z = (y + z) · x ＝ (y · x) + (z · x)

-- semirings (nonabsorptive)

record is-semiring {A : 𝒰 ℓ}
    (_+_ : A → A → A)
    (_·_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field +-comm-monoid : is-comm-monoid _+_
  open is-comm-monoid +-comm-monoid public
    hiding ( Pointed-is-monoid ; Has-binary-op-is-n-magma
           ; Assoc-semigroup ; Unit-l-monoid ; Unit-r-monoid
           )
    renaming ( id    to 0a
             ; assoc to +-assoc
             ; id-l  to +-id-l
             ; id-r  to +-id-r
             ; comm  to +-comm
             ; has-unital-magma to has-unital-magma-+
             )

  field ·-monoid : is-monoid _·_
  open is-monoid ·-monoid public
    hiding ( has-is-of-hlevel ; H-Level-magma-carrier
           ; Pointed-is-monoid ; Has-binary-op-is-n-magma
           ; Assoc-semigroup ; Unit-l-monoid ; Unit-r-monoid
           )
    renaming ( id    to 1a
             ; assoc to ·-assoc
             ; id-l  to ·-id-l
             ; id-r  to ·-id-r
             ; has-unital-magma to has-unital-magma-·
             )

  field
    ·-distrib-+-l : Π[ Distrib-l _·_ _+_ ]
    ·-distrib-+-r : Π[ Distrib-r _·_ _+_ ]

unquoteDecl is-semiring-iso = declare-record-iso is-semiring-iso (quote is-semiring)

opaque
  is-semiring-is-prop : is-prop (is-semiring _✦_ _✧_)
  is-semiring-is-prop S = ≅→is-of-hlevel! 1 is-semiring-iso S where
    open is-semiring S

instance opaque
  H-Level-is-semiring : ⦃ n ≥ʰ 1 ⦄ → H-Level n (is-semiring _✦_ _✧_)
  H-Level-is-semiring ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-semiring-is-prop


record Semiring-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _+_ _·_ : X → X → X
    has-semiring : is-semiring _+_ _·_

  open is-semiring has-semiring public
  infixr 20 _+_
  infixr 30 _·_

unquoteDecl semiring-on-iso = declare-record-iso semiring-on-iso (quote Semiring-on)

opaque
  semiring-on-is-set : is-set (Semiring-on A)
  semiring-on-is-set = ≅→is-of-hlevel 2 semiring-on-iso λ (_ , _ , x) _ _ _ →
    let open is-semiring x in prop!


record Semiring-hom
  {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′} (e : A → B)
  (M : Semiring-on A) (M′ : Semiring-on B) : 𝒰 (ℓ ⊔ ℓ′)
  where
    no-eta-equality
    private
      module A = Semiring-on M
      module B = Semiring-on M′

    field
      pres-0 : e A.0a ＝ B.0a
      pres-1 : e A.1a ＝ B.1a
      pres-+  : (x y : A) → e (x A.+ y) ＝ e x B.+ e y
      pres-·  : (x y : A) → e (x A.· y) ＝ e x B.· e y

unquoteDecl semiring-hom-iso = declare-record-iso semiring-hom-iso (quote Semiring-hom)

opaque
  semiring-hom-is-prop : ∀ {M : Semiring-on A} {M′ : Semiring-on B} {f}
                       → is-prop (Semiring-hom f M M′)
  semiring-hom-is-prop {M′} = ≅→is-of-hlevel! 1 semiring-hom-iso where
    open Semiring-on M′

instance opaque
  H-Level-semiring-on : ⦃ n ≥ʰ 2 ⦄ → H-Level n (Semiring-on A)
  H-Level-semiring-on ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 semiring-on-is-set

  H-Level-semiring-hom : ⦃ n ≥ʰ 1 ⦄ → ∀ {M : Semiring-on A} {M′ : Semiring-on B} {f}
                       → H-Level n (Semiring-hom f M M′)
  H-Level-semiring-hom ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance semiring-hom-is-prop

instance
  ⇒-Semiring : ⇒-notation (Σ[ X ꞉ Type ℓ ] Semiring-on X) (Σ[ Y ꞉ Type ℓ′ ] Semiring-on Y) (𝒰 (ℓ ⊔ ℓ′))
  ⇒-Semiring .⇒-notation.Constraint _ _ = ⊤
  ⇒-Semiring ._⇒_ (A , X) (B , Y) = Total-hom Fun Semiring-hom X Y

  Refl-Semiring-hom : Refl {A = Semiring-on A} (Semiring-hom refl)
  Refl-Semiring-hom .refl .Semiring-hom.pres-+ _ _ = refl
  Refl-Semiring-hom .refl .Semiring-hom.pres-· _ _ = refl
  Refl-Semiring-hom .refl .Semiring-hom.pres-0 = refl
  Refl-Semiring-hom .refl .Semiring-hom.pres-1 = refl

  Comp-Semiring-hom
    : {f : A → B} {g : B → C}
    → Comp (Semiring-hom f) (Semiring-hom g) (Semiring-hom (f ∙ g))
  Comp-Semiring-hom {f} {g} ._∙_ p q .Semiring-hom.pres-+ a a′ =
    ap g (p .Semiring-hom.pres-+ a a′) ∙ q .Semiring-hom.pres-+ (f a) (f a′)
  Comp-Semiring-hom {f} {g} ._∙_ p q .Semiring-hom.pres-· a a′ =
    ap g (p .Semiring-hom.pres-· a a′) ∙ q .Semiring-hom.pres-· (f a) (f a′)
  Comp-Semiring-hom {f} {g} ._∙_ p q .Semiring-hom.pres-0 =
    ap g (p .Semiring-hom.pres-0) ∙ q .Semiring-hom.pres-0
  Comp-Semiring-hom {f} {g} ._∙_ p q .Semiring-hom.pres-1 =
    ap g (p .Semiring-hom.pres-1) ∙ q .Semiring-hom.pres-1

semiring-on→additive-comm-monoid-on : ∀[ Semiring-on {ℓ} ⇒ CMonoid-on ]
semiring-on→additive-comm-monoid-on S = to-comm-monoid-on go where
  open Semiring-on S
  go : make-comm-monoid _
  go .make-comm-monoid.monoid-is-set = hlevel!
  go .make-comm-monoid.id = 0a
  go .make-comm-monoid._⋆_ = _+_
  go .make-comm-monoid.id-l = +-id-l
  go .make-comm-monoid.id-r = +-id-r
  go .make-comm-monoid.assoc = +-assoc
  go .make-comm-monoid.comm = +-comm

semiring-on→multiplicative-monoid-on : ∀[ Semiring-on {ℓ} ⇒ Monoid-on ]
semiring-on→multiplicative-monoid-on S = to-monoid-on go where
  open Semiring-on S
  go : make-monoid _
  go .make-monoid.monoid-is-set = hlevel!
  go .make-monoid.id = 1a
  go .make-monoid._⋆_ = _·_
  go .make-monoid.id-l = ·-id-l
  go .make-monoid.id-r = ·-id-r
  go .make-monoid.assoc = ·-assoc


record make-semiring {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    semiring-is-set : is-set X
    0a 1a : X
    _+_ _·_ : X → X → X
    +-id-l  : Π[ Unitality-l X 0a _+_ ]
    +-id-r  : Π[ Unitality-r X 0a _+_ ]
    +-assoc : Π[ Associativity X _+_ ]
    +-comm  : Π[ Commutativity X _+_ ]
    ·-id-l  : Π[ Unitality-l X 1a _·_ ]
    ·-id-r  : Π[ Unitality-r X 1a _·_ ]
    ·-assoc : Π[ Associativity X _·_ ]
    ·-distrib-+-l : Π[ Distrib-l _·_ _+_ ]
    ·-distrib-+-r : Π[ Distrib-r _·_ _+_ ]

  to-is-semiring : is-semiring _+_ _·_
  to-is-semiring .is-semiring.+-comm-monoid = to-is-comm-monoid go where
    go : make-comm-monoid X
    go .make-comm-monoid.monoid-is-set = semiring-is-set
    go .make-comm-monoid.id = 0a
    go .make-comm-monoid._⋆_ = _+_
    go .make-comm-monoid.id-l = +-id-l
    go .make-comm-monoid.id-r = +-id-r
    go .make-comm-monoid.assoc = +-assoc
    go .make-comm-monoid.comm = +-comm
  to-is-semiring .is-semiring.·-monoid = to-is-monoid go where
    go : make-monoid X
    go .make-monoid.monoid-is-set = semiring-is-set
    go .make-monoid.id = 1a
    go .make-monoid._⋆_ = _·_
    go .make-monoid.id-l = ·-id-l
    go .make-monoid.id-r = ·-id-r
    go .make-monoid.assoc = ·-assoc
  to-is-semiring .is-semiring.·-distrib-+-l = ·-distrib-+-l
  to-is-semiring .is-semiring.·-distrib-+-r = ·-distrib-+-r

  to-semiring-on : Semiring-on X
  to-semiring-on .Semiring-on._+_ = _+_
  to-semiring-on .Semiring-on._·_ = _·_
  to-semiring-on .Semiring-on.has-semiring = to-is-semiring

open make-semiring using (to-is-semiring ; to-semiring-on) public
