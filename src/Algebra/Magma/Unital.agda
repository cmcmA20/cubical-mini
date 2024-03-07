{-# OPTIONS --safe #-}
module Algebra.Magma.Unital where

open import Categories.Prelude

open import Algebra.Magma public

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  e x y z : A
  _✦_ : A → A → A
  n : HLevel

Unital-left : (id : A) (_⋆_ : A → A → A) → 𝒰 _
Unital-left {A} id _⋆_ = Π[ x ꞉ A ] (id ⋆ x ＝ x)

Unital-right : (id : A) (_⋆_ : A → A → A) → 𝒰 _
Unital-right {A} id _⋆_ = Π[ x ꞉ A ] (x ⋆ id ＝ x)

-- unital magmas

record is-unital-magma {A : 𝒰 ℓ} (id : A) (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-magma : is-magma _⋆_
  open is-n-magma has-magma public

  field
    id-l : Unital-left  id _⋆_
    id-r : Unital-right id _⋆_

unquoteDecl is-unital-magma-iso = declare-record-iso is-unital-magma-iso (quote is-unital-magma)

opaque
  unfolding is-of-hlevel
  is-unital-magma-is-prop : is-prop (is-unital-magma e _✦_)
  is-unital-magma-is-prop C = iso→is-of-hlevel 1 is-unital-magma-iso hlevel! C where
    open is-unital-magma C

instance
  H-Level-is-unital-magma : H-Level (suc n) (is-unital-magma e _✦_)
  H-Level-is-unital-magma = hlevel-prop-instance is-unital-magma-is-prop

identity-unique
  : (e e′ : A)
  → is-unital-magma e _✦_
  → is-unital-magma e′ _✦_
  → e ＝ e′
identity-unique {_✦_} e e′ u u′ =
  e       ＝˘⟨ is-unital-magma.id-r u′ e ⟩
  e ✦ e′  ＝⟨ is-unital-magma.id-l u e′ ⟩
  e′      ∎

opaque
  unfolding is-of-hlevel
  has-identity-is-prop
    : {A : 𝒰 ℓ} {_✦_ : A → A → A}
    → is-magma _✦_
    → is-prop (Σ[ id ꞉ A ] is-unital-magma id _✦_)
  has-identity-is-prop m u u′ = Σ-prop-path! (identity-unique _ _ (u .snd) (u′ .snd))


record UMagma-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    id  : X
    _⋆_ : X → X → X
    has-unital-magma : is-unital-magma id _⋆_

  open is-unital-magma has-unital-magma public
  infixr 20 _⋆_

unquoteDecl umagma-on-iso = declare-record-iso umagma-on-iso (quote UMagma-on)

umagma-on-is-set : is-set (UMagma-on A)
umagma-on-is-set = iso→is-of-hlevel _ umagma-on-iso $ is-set-η λ (_ , _ , x) _ _ _ →
  let open is-unital-magma x in prop!


record UMagma-hom
  {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
  (M : UMagma-on A) (M′ : UMagma-on B) (e : A → B) : 𝒰 (ℓ ⊔ ℓ′)
  where
    no-eta-equality
    private
      module A = UMagma-on M
      module B = UMagma-on M′

    field
      pres-id : e A.id ＝ B.id
      pres-⋆  : (x y : A) → e (x A.⋆ y) ＝ e x B.⋆ e y

unquoteDecl umagma-hom-iso = declare-record-iso umagma-hom-iso (quote UMagma-hom)

umagma-hom-is-prop : ∀ {M : UMagma-on A} {M′ : UMagma-on B} {f}
                   → is-prop (UMagma-hom M M′ f)
umagma-hom-is-prop {M′} = iso→is-of-hlevel _ umagma-hom-iso hlevel! where
  open UMagma-on M′

instance
  H-Level-umagma-on : H-Level (2 + n) (UMagma-on A)
  H-Level-umagma-on = hlevel-basic-instance 2 umagma-on-is-set

  H-Level-umagma-hom : ∀ {M : UMagma-on A} {M′ : UMagma-on B} {f}
                     → H-Level (suc n) (UMagma-hom M M′ f)
  H-Level-umagma-hom = hlevel-prop-instance umagma-hom-is-prop

unital-magma-on↪magma-on : UMagma-on A ↪ₜ Magma-on A
unital-magma-on↪magma-on .fst M .n-Magma-on._⋆_ = M .UMagma-on._⋆_
unital-magma-on↪magma-on .fst M .n-Magma-on.has-n-magma = M .UMagma-on.has-magma
unital-magma-on↪magma-on .snd = set-injective→is-embedding hlevel! λ {x} {y} p →
  Equiv.injective (isoₜ→equiv umagma-on-iso) $
    let u = ap n-Magma-on._⋆_ p
        v = identity-unique (UMagma-on.id x) (UMagma-on.id y)
              (UMagma-on.has-unital-magma x)
              (subst (is-unital-magma _) (sym u) (UMagma-on.has-unital-magma y))
    in v ,ₚ u ,ₚ prop!


record make-unital-magma {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    unital-magma-is-set : is-set X
    id  : X
    _⋆_ : X → X → X
    id-l  : Unital-left  id _⋆_
    id-r  : Unital-right id _⋆_

  to-is-unital-magma : is-unital-magma id _⋆_
  to-is-unital-magma .is-unital-magma.has-magma .is-n-magma.has-is-of-hlevel =
    unital-magma-is-set
  to-is-unital-magma .is-unital-magma.id-l = id-l
  to-is-unital-magma .is-unital-magma.id-r = id-r

  to-unital-magma-on : UMagma-on X
  to-unital-magma-on .UMagma-on.id = id
  to-unital-magma-on .UMagma-on._⋆_ = _⋆_
  to-unital-magma-on .UMagma-on.has-unital-magma = to-is-unital-magma

open make-unital-magma using (to-is-unital-magma ; to-unital-magma-on) public
