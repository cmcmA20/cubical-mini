{-# OPTIONS --safe --no-exact-split #-}
module Order.Strict where

open import Cat.Prelude

open import Meta.Projection
open import Meta.Reflection.Base

open import Order.Base
open import Data.Sum.Base
open import Data.Sum.Path

private variable n : HLevel

record StrictPoset o ℓ : 𝒰 (ℓsuc (o ⊔ ℓ)) where
  no-eta-equality
  infix 4.5 _<_
  field
    Ob  : 𝒰 o
    _<_ : Ob → Ob → 𝒰 ℓ
    <-thin    : ∀ {x y} → is-prop (x < y)
    <-irrefl  : ∀ {x} → ¬ (x < x)
    <-trans   : ∀ {x y z} → x < y → y < z → x < z

  instance opaque
    H-Level-<-prop : ∀ {x y} → H-Level (suc n) (x < y)
    H-Level-<-prop = hlevel-prop-instance <-thin

  instance
    Trans-< : Trans _<_
    Trans-< ._∙_ = <-trans
    {-# OVERLAPPING Trans-< #-}

    HAssoc-< : HAssoc _<_
    HAssoc-< .∙-assoc _ _ _ = prop!

  _>_ _≮_ _≯_ : Ob → Ob → 𝒰 ℓ
  _>_ = flip _<_
  _≮_ x y = ¬ x < y
  _≯_ x y = ¬ x > y

  <-asym : ∀ {x y} → x < y → y ≮ x
  <-asym x<y y<x = <-irrefl (x<y ∙ y<x)

  <→≠ : ∀ {x y} → x < y → x ≠ y
  <→≠ {x} x<y x=y = <-irrefl (subst (x <_) (x=y ⁻¹) x<y)

  =→≮ : ∀ {x y} → x ＝ y → x ≮ y
  =→≮ = flip <→≠

  reflexive-closure : ⦃ _ : H-Level 2 Ob ⦄ → Poset o (o ⊔ ℓ)
  reflexive-closure .Poset.Ob = Ob
  reflexive-closure .Poset._≤_ x y = (x < y) ⊎ (x ＝ y)
  reflexive-closure .Poset.≤-thin {x} {y} = disjoint-⊎-is-prop! (<→≠ $ₜ²_)
  reflexive-closure .Poset.≤-refl = inr refl
  reflexive-closure .Poset.≤-trans (inl x<y) (inl y<z) = inl (x<y ∙ y<z)
  reflexive-closure .Poset.≤-trans (inl x<y) (inr y=z) = inl (subst (_ <_) y=z x<y)
  reflexive-closure .Poset.≤-trans (inr x=y) (inl y<z) = inl (subst (_< _) (sym x=y) y<z)
  reflexive-closure .Poset.≤-trans (inr x=y) (inr y=z) = inr (x=y ∙ y=z)
  reflexive-closure .Poset.≤-antisym (inl x<y) (inl y<x) = ⊥.rec (<-asym x<y y<x)
  reflexive-closure .Poset.≤-antisym (inl x<y) (inr y=x) = ⊥.rec (<→≠ x<y (sym y=x))
  reflexive-closure .Poset.≤-antisym (inr x=y) (inl y<x) = ⊥.rec (<→≠ y<x (sym x=y))
  reflexive-closure .Poset.≤-antisym (inr x=y) _ = x=y

unquoteDecl strict-poset-iso = declare-record-iso strict-poset-iso (quote StrictPoset)

private variable o ℓ : Level

-- aka irreflexive kernel
reflexive-reduction : Poset o ℓ → StrictPoset o (o ⊔ ℓ)
reflexive-reduction P .StrictPoset.Ob = P .Poset.Ob
reflexive-reduction P .StrictPoset._<_ x y = (P .Poset._≤_ x y) × (x ≠ y)
reflexive-reduction P .StrictPoset.<-thin = hlevel 1
reflexive-reduction P .StrictPoset.<-irrefl (_ , ne) = ne refl
reflexive-reduction P .StrictPoset.<-trans (lxy , nxy) (lyz , nyz)
  = lxy ∙ lyz
  , λ x=z → nyz (≤-antisym lyz (subst (_≤ _) x=z lxy))
  where open Poset P

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
