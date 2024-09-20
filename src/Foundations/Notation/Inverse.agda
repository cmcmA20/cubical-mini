{-# OPTIONS --safe #-}
module Foundations.Notation.Inverse where

open import Foundations.Prim.Type

open import Foundations.Notation.Composition
open import Foundations.Notation.Duality
open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Retraction
open import Foundations.Notation.Section

module _
  {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ ℓ‴ : Level}
  {F : A → B → 𝒰 ℓ′} {G : B → A → 𝒰 ℓ}
  {F∙G : A → A → 𝒰 ℓ″} {G∙F : B → B → 𝒰 ℓ‴}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄ where

  record Inverses {x : A} {y : B} (f : F x y) (g : G y x) : 𝒰 (ℓ″ ⊔ ℓ‴) where
    no-eta-equality
    constructor make-inverses
    field
      inv-o : f retraction-of g
      inv-i : f section-of g
  {-# INLINE make-inverses #-}

record is-invertible
  {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ ℓ‴ : Level}
  {F : A → B → 𝒰 ℓ′} {G : B → A → 𝒰 ℓ}
  {F∙G : A → A → 𝒰 ℓ″} {G∙F : B → B → 𝒰 ℓ‴}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
  {x : A} {y : B} (f : F x y) : 𝒰 (ℓ ⊔ ℓ″ ⊔ ℓ‴) where
  no-eta-equality
  constructor make-invertible
  field
    inv      : G y x
    inverses : Inverses f inv

  open Inverses inverses public

  op : is-invertible inv
  op .inv = f
  op .inverses .Inverses.inv-o = inv-i
  op .inverses .Inverses.inv-i = inv-o
{-# INLINE make-invertible #-}


module _
  {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ ℓ‴ : Level}
  {F : A → B → 𝒰 ℓ′} {G : B → A → 𝒰 ℓ}
  {F∙G : A → A → 𝒰 ℓ″} {G∙F : B → B → 𝒰 ℓ‴}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
  {x : A} {y : B} {f : F x y} where

  invertible : (g : G y x) → f retraction-of g → f section-of g
             → is-invertible f
  invertible g r s .is-invertible.inv = g
  invertible g r s .is-invertible.inverses .Inverses.inv-o = r
  invertible g r s .is-invertible.inverses .Inverses.inv-i = s
  {-# INLINE invertible #-}

  inverses→is-inv : {g : G y x} → Inverses f g → is-invertible f
  inverses→is-inv {g} i .is-invertible.inv = g
  inverses→is-inv     i .is-invertible.inverses = i
  {-# INLINE inverses→is-inv #-}

  is-inv→has-section : is-invertible f → has-section f
  is-inv→has-section i .section = i .is-invertible.inv
  is-inv→has-section i .is-section = i .is-invertible.inverses .Inverses.inv-o
  {-# INLINE is-inv→has-section #-}


instance
  Dual-Inverses
    : ∀ {ℓᵃ ℓᵇ ℓᵃ̇ ℓᵇ̇ ℓ ℓ′} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
      {F : A → B → 𝒰 ℓ}  {G : B → A → 𝒰 ℓ′}
      {U : A → A → 𝒰 ℓᵃ̇} {V : B → B → 𝒰 ℓᵇ̇}
      ⦃ _ : Comp F G U ⦄ ⦃ _ : Comp G F V ⦄
      ⦃ _ : Refl U ⦄      ⦃ _ : Refl V ⦄
      {x : A} {y : B}
    → Dual (Inverses {F = F} {G = G} {x = x} {y = y}) Inverses
  Dual-Inverses ._ᵒᵖ i .Inverses.inv-o = Inverses.inv-i i
  Dual-Inverses ._ᵒᵖ i .Inverses.inv-i = Inverses.inv-o i
