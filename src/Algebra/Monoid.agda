{-# OPTIONS --safe #-}
module Algebra.Monoid where

open import Categories.Prelude

open import Algebra.Semigroup public

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ
  e x y : A
  _✦_ : A → A → A
  n : HLevel

Unital-left : (id : A) (_⋆_ : A → A → A) → 𝒰 _
Unital-left {A} id _⋆_ = Π[ x ꞉ A ] (id ⋆ x ＝ x)

Unital-right : (id : A) (_⋆_ : A → A → A) → 𝒰 _
Unital-right {A} id _⋆_ = Π[ x ꞉ A ] (x ⋆ id ＝ x)

-- monoids

record is-monoid {A : 𝒰 ℓ} (id : A) (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-semigroup : is-semigroup _⋆_
  open is-semigroup has-semigroup public

  field
    id-l : Unital-left  id _⋆_
    id-r : Unital-right id _⋆_

unquoteDecl is-monoid-iso = declare-record-iso is-monoid-iso (quote is-monoid)

opaque
  unfolding is-of-hlevel
  is-monoid-is-prop : is-prop (is-monoid e _✦_)
  is-monoid-is-prop M = iso→is-of-hlevel 1 is-monoid-iso hlevel! M where
    open is-monoid M

instance
  H-Level-is-monoid : H-Level (suc n) (is-monoid e _✦_)
  H-Level-is-monoid = hlevel-prop-instance is-monoid-is-prop


record Monoid-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    id  : X
    _⋆_ : X → X → X
    has-monoid : is-monoid id _⋆_

  open is-monoid has-monoid public
  infixr 20 _⋆_

unquoteDecl monoid-on-iso = declare-record-iso monoid-on-iso (quote Monoid-on)

monoid-on-is-set : is-set (Monoid-on A)
monoid-on-is-set = iso→is-of-hlevel _ monoid-on-iso $ is-set-η λ (_ , _ , x) _ _ _ →
  let open is-monoid x in prop!


record Monoid-hom
  {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
  (M : Monoid-on A) (M′ : Monoid-on B) (e : A → B) : 𝒰 (ℓ ⊔ ℓ′)
  where
    no-eta-equality
    private
      module A = Monoid-on M
      module B = Monoid-on M′

    field
      pres-id : e A.id ＝ B.id
      pres-⋆  : (x y : A) → e (x A.⋆ y) ＝ e x B.⋆ e y

unquoteDecl monoid-hom-iso = declare-record-iso monoid-hom-iso (quote Monoid-hom)

monoid-hom-is-prop : ∀ {M : Monoid-on A} {M′ : Monoid-on B} {f}
                   → is-prop (Monoid-hom M M′ f)
monoid-hom-is-prop {M′} = iso→is-of-hlevel _ monoid-hom-iso hlevel! where
  open Monoid-on M′

instance
  H-Level-monoid-on : H-Level (2 + n) (Monoid-on A)
  H-Level-monoid-on = hlevel-basic-instance 2 monoid-on-is-set

  H-Level-monoid-hom : ∀ {M : Monoid-on A} {M′ : Monoid-on B} {f}
                     → H-Level (suc n) (Monoid-hom M M′ f)
  H-Level-monoid-hom = hlevel-prop-instance monoid-hom-is-prop

monoid-on→semigroup-on : ∀[ Monoid-on {ℓ} →̇ Semigroup-on {ℓ} ]
monoid-on→semigroup-on M .Semigroup-on._⋆_ = M .Monoid-on._⋆_
monoid-on→semigroup-on M .Semigroup-on.has-semigroup =
  M .Monoid-on.has-monoid .is-monoid.has-semigroup


record make-monoid {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    monoid-is-set : is-set X
    id  : X
    _⋆_ : X → X → X
    id-l : Unital-left  id _⋆_
    id-r : Unital-right id _⋆_
    assoc : Associative _⋆_

  to-is-monoid : is-monoid id _⋆_
  to-is-monoid .is-monoid.has-semigroup = to-is-semigroup sg where
    sg : make-semigroup X
    sg .make-semigroup.semigroup-is-set = monoid-is-set
    sg .make-semigroup._⋆_ = _⋆_
    sg .make-semigroup.assoc = assoc
  to-is-monoid .is-monoid.id-l = id-l
  to-is-monoid .is-monoid.id-r = id-r

  to-monoid-on : Monoid-on X
  to-monoid-on .Monoid-on.id = id
  to-monoid-on .Monoid-on._⋆_ = _⋆_
  to-monoid-on .Monoid-on.has-monoid = to-is-monoid

open make-monoid using (to-is-monoid ; to-monoid-on) public


-- monoid theory
module _ {M : Monoid-on A} where
  open Monoid-on M

  iter-l : ℕ → A → A
  iter-l 0       _ = id
  iter-l (suc n) x = iter-l n x ⋆ x

  iter-r : ℕ → A → A
  iter-r 0       _ = id
  iter-r (suc n) x = x ⋆ iter-r n x

  iter-comm : (n : ℕ) → x ⋆ iter-r n x ＝ iter-r n x ⋆ x
  iter-comm 0       = id-r _ ∙ sym (id-l _)
  iter-comm (suc n) = ap (_ ⋆_) (iter-comm n) ∙ assoc _ _ _

  iter-unique : (n : ℕ) → iter-l n x ＝ iter-r n x
  iter-unique 0       = refl
  iter-unique (suc n) = ap (_⋆ _) (iter-unique n) ∙ sym (iter-comm n)
