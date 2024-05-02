{-# OPTIONS --safe #-}
module Algebra.Monoid.Commutative where

open import Categories.Prelude

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

record is-comm-monoid {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-monoid : is-monoid _⋆_
  open is-monoid has-monoid public

  field comm : Commutative _⋆_

unquoteDecl is-comm-monoid-iso = declare-record-iso is-comm-monoid-iso (quote is-comm-monoid)

opaque
  is-comm-monoid-is-prop : is-prop (is-comm-monoid _✦_)
  is-comm-monoid-is-prop C = ≅→is-of-hlevel! 1 is-comm-monoid-iso C where
    open is-comm-monoid C

instance opaque
  H-Level-is-comm-monoid : H-Level (suc n) (is-comm-monoid _✦_)
  H-Level-is-comm-monoid = hlevel-prop-instance is-comm-monoid-is-prop

record CMonoid-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _⋆_ : X → X → X
    has-comm-monoid : is-comm-monoid _⋆_

  open is-comm-monoid has-comm-monoid public
  infixr 20 _⋆_

unquoteDecl cmonoid-on-iso = declare-record-iso cmonoid-on-iso (quote CMonoid-on)


comm-monoid-on↪monoid-on : CMonoid-on A ↪ₜ Monoid-on A
comm-monoid-on↪monoid-on .fst M .Monoid-on._⋆_ = M .CMonoid-on._⋆_
comm-monoid-on↪monoid-on .fst M .Monoid-on.has-monoid =
  M .CMonoid-on.has-comm-monoid .is-comm-monoid.has-monoid
comm-monoid-on↪monoid-on .snd = set-injective→is-embedding! λ p →
  Equiv.injective (≅ₜ→≃ cmonoid-on-iso) $
    ap Monoid-on._⋆_ p ,ₚ prop!


record make-comm-monoid {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    monoid-is-set : is-set X
    id  : X
    _⋆_ : X → X → X
    id-l  : Unital-left  id _⋆_
    id-r  : Unital-right id _⋆_
    assoc : Associative _⋆_
    comm  : Commutative _⋆_

  to-is-comm-monoid : is-comm-monoid _⋆_
  to-is-comm-monoid .is-comm-monoid.has-monoid = to-is-monoid go where
    go : make-monoid X
    go .make-monoid.monoid-is-set = monoid-is-set
    go .make-monoid.id = id
    go .make-monoid._⋆_ = _⋆_
    go .make-monoid.id-l = id-l
    go .make-monoid.id-r = id-r
    go .make-monoid.assoc = assoc
  to-is-comm-monoid .is-comm-monoid.comm = comm

  to-comm-monoid-on : CMonoid-on X
  to-comm-monoid-on .CMonoid-on._⋆_ = _⋆_
  to-comm-monoid-on .CMonoid-on.has-comm-monoid = to-is-comm-monoid

open make-comm-monoid using (to-is-comm-monoid ; to-comm-monoid-on) public


-- abelian monoid theory

module _ {M : CMonoid-on A} where
  open CMonoid-on M

  exchange
    : {x y z : A}
    → (x ∙ y) ∙ z ＝ (x ∙ z) ∙ y
  exchange {x} {y} {z} =
    (x ∙ y) ∙ z    ＝˘⟨ assoc _ _ _ ⟩
    x ⋆ ⌜ y ⋆ z ⌝  ＝⟨ ap! (comm _ _) ⟩
    x ∙ (z  ∙ y)   ＝⟨ assoc _ _ _ ⟩
    (x ∙ z) ∙ y    ∎
