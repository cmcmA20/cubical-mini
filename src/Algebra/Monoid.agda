{-# OPTIONS --safe #-}
module Algebra.Monoid where

open import Categories.Prelude

open import Algebra.Magma.Unital public
open import Algebra.Semigroup public

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ
  e x y : A
  _✦_ : A → A → A
  n : HLevel

Inverse-left : (id : A) (_⋆_ : A → A → A) (inv : A → A) → 𝒰 _
Inverse-left {A} id _⋆_ inv = Π[ x ꞉ A ] (inv x ⋆ x ＝ id)

Inverse-right : (id : A) (_⋆_ : A → A → A) (inv : A → A) → 𝒰 _
Inverse-right {A} id _⋆_ inv = Π[ x ꞉ A ] (x ⋆ inv x ＝ id)

-- monoids

record is-monoid {A : 𝒰 ℓ} (id : A) (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-semigroup : is-semigroup _⋆_
  open is-semigroup has-semigroup public

  field
    id-l : Unital-left  id _⋆_
    id-r : Unital-right id _⋆_

  has-unital-magma : is-unital-magma id _⋆_
  has-unital-magma .is-unital-magma.has-magma = has-magma
  has-unital-magma .is-unital-magma.id-l = id-l
  has-unital-magma .is-unital-magma.id-r = id-r

unquoteDecl is-monoid-iso = declare-record-iso is-monoid-iso (quote is-monoid)

opaque
  unfolding is-of-hlevel
  is-monoid-is-prop : is-prop (is-monoid e _✦_)
  is-monoid-is-prop M = iso→is-of-hlevel 1 is-monoid-iso hlevel! M where
    open is-monoid M

instance
  H-Level-is-monoid : H-Level (suc n) (is-monoid e _✦_)
  H-Level-is-monoid = hlevel-prop-instance is-monoid-is-prop

module _ {id : A} {IM : is-monoid id _✦_} where
  open is-monoid IM
  monoid-inverse-unique : (e x y : A) → x ✦ e ＝ id → e ✦ y ＝ id → x ＝ y
  monoid-inverse-unique e x y p q =
    x              ＝˘⟨ id-r _ ⟩
    x ✦ ⌜ id ⌝     ＝˘⟨ ap¡ q ⟩
    x ✦ (e ✦ y)    ＝⟨ assoc _ _ _ ⟩
    ⌜ x ✦ e ⌝ ✦ y  ＝⟨ ap! p ⟩
    id ✦ y         ＝⟨ id-l _ ⟩
    y              ∎


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

monoid-on↪semigroup-on : Monoid-on A ↪ₜ Semigroup-on A
monoid-on↪semigroup-on .fst M .Semigroup-on._⋆_ = M .Monoid-on._⋆_
monoid-on↪semigroup-on .fst M .Semigroup-on.has-semigroup =
  M .Monoid-on.has-monoid .is-monoid.has-semigroup
monoid-on↪semigroup-on .snd = set-injective→is-embedding hlevel! λ {x} {y} p →
  Equiv.injective (isoₜ→equiv monoid-on-iso) $
    let u = ap Semigroup-on._⋆_ p
        v = identity-unique (Monoid-on.id x) (Monoid-on.id y)
              (Monoid-on.has-unital-magma x)
              (subst (is-unital-magma _) (sym u) (Monoid-on.has-unital-magma y))
    in v ,ₚ u ,ₚ prop!

-- TODO abstract this proof pattern
monoid-on↪unital-magma-on : Monoid-on A ↪ₜ UMagma-on A
monoid-on↪unital-magma-on .fst M .UMagma-on.id = M .Monoid-on.id
monoid-on↪unital-magma-on .fst M .UMagma-on._⋆_ = M .Monoid-on._⋆_
monoid-on↪unital-magma-on .fst M .UMagma-on.has-unital-magma = Monoid-on.has-unital-magma M
monoid-on↪unital-magma-on .snd = set-injective→is-embedding hlevel! λ {x} {y} p →
  Equiv.injective (isoₜ→equiv monoid-on-iso) $
    let u = ap UMagma-on._⋆_ p
        v = identity-unique (Monoid-on.id x) (Monoid-on.id y)
              (Monoid-on.has-unital-magma x)
              (subst (is-unital-magma _) (sym u) (Monoid-on.has-unital-magma y))
    in v ,ₚ u ,ₚ prop!


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

Endo-on : (X : Set ℓ) → Monoid-on (X →̇ X)
Endo-on X = to-monoid-on go where
  open make-monoid
  go : make-monoid (X →̇ X)
  go .monoid-is-set = hlevel!
  go .id = idₜ
  go ._⋆_ f g = f ∘′ g
  go .id-l _ = refl
  go .id-r _ = refl
  go .assoc _ _ _ = refl
