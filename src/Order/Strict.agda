{-# OPTIONS --safe --no-exact-split #-}
module Order.Strict where

open import Cat.Prelude

open import Meta.Projection
open import Meta.Reflection.Base

private variable n : HLevel

record StrictPoset o ℓ : 𝒰 (ℓsuc (o ⊔ ℓ)) where
  no-eta-equality
  field
    Ob  : 𝒰 o
    _<_ : Ob → Ob → 𝒰 ℓ
    <-thin    : ∀ {x y} → is-prop (x < y)
    <-irrefl    : ∀ {x} → ¬ (x < x)
    <-trans   : ∀ {x y z} → x < y → y < z → x < z

  instance opaque
    H-Level-<-prop : ∀ {x y} → H-Level (suc n) (x < y)
    H-Level-<-prop = hlevel-prop-instance <-thin

  instance
    Trans-< : Trans _<_
    Trans-< ._∙_ = <-trans
    {-# OVERLAPPING Trans-< #-}

    HAssoc-≤ : HAssoc _<_
    HAssoc-≤ .∙-assoc _ _ _ = prop!

  <-asym : ∀ {x y} → x < y → ¬ (y < x)
  <-asym x<y y<x = <-irrefl (<-trans x<y y<x)

  <→≠ : ∀ {x y} → x < y → x ≠ y
  <→≠ {x} x<y x=y = <-irrefl (subst (x <_) (x=y ⁻¹) x<y)

  =→≮ : ∀ {x y} → x ＝ y → ¬ (x < y)
  =→≮ {x} x=y x<y = <-irrefl (subst (x <_) (x=y ⁻¹) x<y)

unquoteDecl strictposet-iso = declare-record-iso strictposet-iso (quote StrictPoset)

private variable o ℓ : Level

instance
  Underlying-StrictPoset : Underlying (StrictPoset o ℓ)
  Underlying-StrictPoset .Underlying.ℓ-underlying = _
  Underlying-StrictPoset .Underlying.⌞_⌟ = StrictPoset.Ob

  open Struct-proj-desc

  Dual-StrictPoset : Has-unary-op (StrictPoset o ℓ)
  Dual-StrictPoset .minv P .StrictPoset.Ob = P .StrictPoset.Ob
  Dual-StrictPoset .minv P .StrictPoset._<_ = flip (P .StrictPoset._<_)
  Dual-StrictPoset .minv P .StrictPoset.<-thin = P. StrictPoset.<-thin
  Dual-StrictPoset .minv P .StrictPoset.<-irrefl = P .StrictPoset.<-irrefl
  Dual-StrictPoset .minv P .StrictPoset.<-trans = flip (P. StrictPoset.<-trans)

  Invol-Dual-StrictPoset : Invol (StrictPoset o ℓ)
  Invol-Dual-StrictPoset .minv-invol P _ .StrictPoset.Ob = P .StrictPoset.Ob
  Invol-Dual-StrictPoset .minv-invol P _ .StrictPoset._<_ = P .StrictPoset._<_
  Invol-Dual-StrictPoset .minv-invol P _ .StrictPoset.<-thin = P .StrictPoset.<-thin
  Invol-Dual-StrictPoset .minv-invol P _ .StrictPoset.<-irrefl = P .StrictPoset.<-irrefl
  Invol-Dual-StrictPoset .minv-invol P _ .StrictPoset.<-trans = P .StrictPoset.<-trans

  ⊥-StrictPoset : ⊥-notation (StrictPoset o ℓ)
  ⊥-StrictPoset .⊥ .StrictPoset.Ob = ⊥
  ⊥-StrictPoset .⊥ .StrictPoset._<_ _ _ = ⊥

