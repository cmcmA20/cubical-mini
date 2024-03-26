{-# OPTIONS --safe #-}
module Algebra.Group where

open import Categories.Prelude

open import Algebra.Monoid public

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ
  e x y : A
  _✦_ : A → A → A
  n : HLevel

-- monoids

record is-group {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field
    inverse : A → A
    has-monoid : is-monoid _⋆_
  open is-monoid has-monoid public

  field
    inverse-l : Inverse-left  id _⋆_ inverse
    inverse-r : Inverse-right id _⋆_ inverse

unquoteDecl is-group-iso = declare-record-iso is-group-iso (quote is-group)

opaque
  unfolding is-of-hlevel
  is-group-is-prop : {_✦_ : A → A → A} → is-prop (is-group _✦_)
  is-group-is-prop {A} {_✦_} M N = Equiv.injective (isoₜ→equiv is-group-iso)
    $  fun-ext (λ a → monoid-inverse-unique {IM = M .is-group.has-monoid} a _ _
         (M .is-group.inverse-l a) (N .is-group.inverse-r a ∙ sym u))
    ,ₚ prop!
    where
      u : M .is-group.id ＝ N .is-group.id
      u = identity-unique (is-monoid.has-unital-magma (M .is-group.has-monoid))
                          (is-monoid.has-unital-magma (N .is-group.has-monoid))
      instance
        A-set : H-Level 2 A
        A-set = hlevel-basic-instance 2 (M .is-group.has-is-of-hlevel)

instance
  H-Level-is-group : H-Level (suc n) (is-group _✦_)
  H-Level-is-group = hlevel-prop-instance is-group-is-prop


record Group-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _⋆_ : X → X → X
    has-group : is-group _⋆_

  open is-group has-group public
  infixr 20 _⋆_

unquoteDecl group-on-iso = declare-record-iso group-on-iso (quote Group-on)

-- TODO
-- instance
--   Inv-group : ⦃ G : Group-on A ⦄ → Invertible small {!!}
--   Inv-group Invertible.⁻¹ = {!inverse!}

group-on-is-set : is-set (Group-on A)
group-on-is-set = iso→is-of-hlevel _ group-on-iso $ is-set-η λ (op , x) _ _ _ →
  let open is-group x in prop!


record Group-hom
  {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
  (M : Group-on A) (M′ : Group-on B) (e : A → B) : 𝒰 (ℓ ⊔ ℓ′)
  where
    no-eta-equality
    private
      module A = Group-on M
      module B = Group-on M′

    field pres-⋆  : (x y : A) → e (x A.⋆ y) ＝ e x B.⋆ e y

    pres-id : e A.id ＝ B.id
    pres-id =
      e A.id                                        ＝˘⟨ B.id-r _ ⟩
      e A.id B.⋆ ⌜ B.id ⌝                           ＝˘⟨ ap¡ (B.inverse-r _) ⟩
      e A.id B.⋆ (e A.id B.⋆ B.inverse (e A.id))    ＝⟨ B.assoc _ _ _ ⟩
      ⌜ e A.id B.⋆ e A.id ⌝ B.⋆ B.inverse (e A.id)  ＝⟨ ap! (sym (pres-⋆ _ _) ∙ ap e (A.id-l _)) ⟩
      e A.id B.⋆ B.inverse (e A.id)                 ＝⟨ B.inverse-r _ ⟩
      B.id                                          ∎

    pres-inv : ∀ x → e (A.inverse x) ＝ B.inverse (e x)
    pres-inv x = monoid-inverse-unique {IM = B.has-monoid} (e x) _ _
      (sym (pres-⋆ _ _) ∙∙ ap e (A.inverse-l _) ∙∙ pres-id)
      (B.inverse-r _)

unquoteDecl group-hom-iso = declare-record-iso group-hom-iso (quote Group-hom)

group-hom-is-prop : ∀ {M : Group-on A} {M′ : Group-on B} {f}
                   → is-prop (Group-hom M M′ f)
group-hom-is-prop {M′} = iso→is-of-hlevel _ group-hom-iso hlevel! where
  open Group-on M′

instance
  H-Level-group-on : H-Level (2 + n) (Group-on A)
  H-Level-group-on = hlevel-basic-instance 2 group-on-is-set

  H-Level-group-hom : ∀ {M : Group-on A} {M′ : Group-on B} {f}
                    → H-Level (suc n) (Group-hom M M′ f)
  H-Level-group-hom = hlevel-prop-instance group-hom-is-prop

group-on↪monoid-on : Group-on A ↪ₜ Monoid-on A
group-on↪monoid-on .fst G .Monoid-on._⋆_ = G .Group-on._⋆_
group-on↪monoid-on .fst G .Monoid-on.has-monoid = G .Group-on.has-monoid
group-on↪monoid-on .snd = set-injective→is-embedding hlevel! λ {x} {y} p →
  Equiv.injective (isoₜ→equiv group-on-iso) $
    ap Monoid-on._⋆_ p ,ₚ prop!


record make-group {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    group-is-set : is-set X
    id  : X
    _⋆_ : X → X → X
    inverse : X → X
    id-l      : Unital-left  id _⋆_
    inverse-l : Inverse-left id _⋆_ inverse
    assoc     : Associative _⋆_

  inverse-r : Inverse-right id _⋆_ inverse
  inverse-r x =
    x ⋆ inverse x                                          ＝˘⟨ id-l _ ⟩
    ⌜ id ⌝ ⋆ (x ⋆ inverse x)                               ＝˘⟨ ap¡ (inverse-l _) ⟩
    (inverse (inverse x) ⋆ inverse x) ⋆ (x ⋆ inverse x)    ＝˘⟨ assoc _ _ _ ⟩
    inverse (inverse x) ⋆ ⌜ inverse x ⋆ (x ⋆ inverse x) ⌝  ＝⟨ ap! (assoc _ _ _) ⟩
    inverse (inverse x) ⋆ (⌜ inverse x ⋆ x ⌝ ⋆ inverse x)  ＝⟨ ap! (inverse-l _) ⟩
    inverse (inverse x) ⋆ ⌜ id ⋆ inverse x ⌝               ＝⟨ ap! (id-l _) ⟩
    inverse (inverse x) ⋆ inverse x                        ＝⟨ inverse-l _ ⟩
    id                                                     ∎

  id-r : Unital-right id _⋆_
  id-r x =
    x ⋆ ⌜ id ⌝             ＝˘⟨ ap¡ (inverse-l _) ⟩
    x ⋆ (inverse x ⋆ x)    ＝⟨ assoc _ _ _ ⟩
    ⌜ x ⋆ inverse x ⌝ ⋆ x  ＝⟨ ap! (inverse-r _) ⟩
    id ⋆ x                 ＝⟨ id-l _ ⟩
    x                      ∎

  to-is-group : is-group _⋆_
  to-is-group .is-group.has-monoid = to-is-monoid m where
    m : make-monoid X
    m .make-monoid.monoid-is-set = group-is-set
    m .make-monoid.id = id
    m .make-monoid._⋆_ = _⋆_
    m .make-monoid.id-l = id-l
    m .make-monoid.id-r = id-r
    m .make-monoid.assoc = assoc
  to-is-group .is-group.inverse = inverse
  to-is-group .is-group.inverse-l = inverse-l
  to-is-group .is-group.inverse-r = inverse-r

  to-group-on : Group-on X
  to-group-on .Group-on._⋆_ = _⋆_
  to-group-on .Group-on.has-group = to-is-group

open make-group using (to-is-group ; to-group-on) public
