{-# OPTIONS --safe #-}
module Algebra.Group.Abelian where

open import Cat.Prelude

open import Algebra.Group public
open import Algebra.Monoid.Commutative public

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  e x y z : A
  _✦_ : A → A → A
  n : HLevel

-- commutative groups

record is-abelian-group {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-group : is-group _⋆_
  open is-group has-group public

  field comm : Π[ Commutativity A _⋆_ ]

unquoteDecl is-abelian-group-iso = declare-record-iso is-abelian-group-iso (quote is-abelian-group)

opaque
  is-abelian-group-is-prop : is-prop (is-abelian-group _✦_)
  is-abelian-group-is-prop C = ≅→is-of-hlevel! 1 is-abelian-group-iso C where
    open is-abelian-group C

instance opaque
  H-Level-is-abelian-group : ⦃ n ≥ʰ 1 ⦄ → H-Level n (is-abelian-group _✦_)
  H-Level-is-abelian-group ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-abelian-group-is-prop

record AGroup-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _⋆_ : X → X → X
    has-abelian-group : is-abelian-group _⋆_

  open is-abelian-group has-abelian-group public
  infixr 20 _⋆_

unquoteDecl agroup-on-iso = declare-record-iso agroup-on-iso (quote AGroup-on)


abelian-group-on↪group-on : AGroup-on A ↪ₜ Group-on A
abelian-group-on↪group-on .fst G .Group-on._⋆_ = G .AGroup-on._⋆_
abelian-group-on↪group-on .fst G .Group-on.has-group =
  G .AGroup-on.has-abelian-group .is-abelian-group.has-group
abelian-group-on↪group-on .snd = set-injective→is-embedding! λ p →
  Equiv.injective (≅ₜ→≃ agroup-on-iso) $ ap Group-on._⋆_ p ,ₚ prop!

instance
  ⇒-AGroup : ⇒-notation (Σ[ X ꞉ Set ℓ ] AGroup-on ⌞ X ⌟) (Σ[ Y ꞉ Set ℓ′ ] AGroup-on ⌞ Y ⌟) (𝒰 (ℓ ⊔ ℓ′))
  ⇒-AGroup ._⇒_ (A , X) (B , Y) = Total-hom (λ P Q → ⌞ P ⌟ → ⌞ Q ⌟)
    (λ f P Q → Group-hom f (abelian-group-on↪group-on .fst P) (abelian-group-on↪group-on .fst Q)) {a = A} {b = B} X Y


record make-abelian-group {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    abelian-group-is-set : is-set X
    id  : X
    _⋆_ : X → X → X
    inverse : X → X
    id-l  : Π[ Unitality-l X id _⋆_ ]
    assoc : Π[ Associativity X _⋆_ ]
    comm  : Π[ Commutativity X _⋆_ ]
    inverse-l : ∀ x → inverse x ⋆ x ＝ id

  private
    go : make-group X
    go .make-group.group-is-set = abelian-group-is-set
    go .make-group.id = id
    go .make-group._⋆_ = _⋆_
    go .make-group.inverse = inverse
    go .make-group.id-l = id-l
    go .make-group.inverse-l = inverse-l
    go .make-group.assoc = assoc

  to-is-abelian-group : is-abelian-group _⋆_
  to-is-abelian-group .is-abelian-group.has-group = to-is-group go
  to-is-abelian-group .is-abelian-group.comm = comm

  to-abelian-group-on : AGroup-on X
  to-abelian-group-on .AGroup-on._⋆_ = _⋆_
  to-abelian-group-on .AGroup-on.has-abelian-group = to-is-abelian-group

  id-r : ∀ x → Unitality-r X id _⋆_ x
  id-r = Group-on.id-r (to-group-on go)

  inverse-r : ∀ x → x ⋆ inverse x ＝ id
  inverse-r = Group-on.inverse-r (to-group-on go)

open make-abelian-group using (to-is-abelian-group ; to-abelian-group-on) public
