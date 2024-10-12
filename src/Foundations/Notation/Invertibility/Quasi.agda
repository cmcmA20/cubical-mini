{-# OPTIONS --safe #-}
module Foundations.Notation.Invertibility.Quasi where

open import Foundations.Prim.Type

open import Foundations.Notation.Composition
open import Foundations.Notation.Duality
open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Retraction
open import Foundations.Notation.Section
open import Foundations.Notation.Unital.Outer

module _
  {ℓa ℓb ℓf ℓg ℓfg ℓgf : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {F : A → B → 𝒰 ℓf} {G : B → A → 𝒰 ℓg}
  {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄ where

  -- not that useful in higher setting
  record Inverses {x : A} {y : B} (f : F x y) (g : G y x) : 𝒰 (ℓfg ⊔ ℓgf) where
    no-eta-equality
    constructor make-inverses
    field
      inv-o : f retraction-of g
      inv-i : f section-of g
  {-# INLINE make-inverses #-}

record quasi-inverse
  {ℓa ℓb ℓf ℓg ℓfg ℓgf : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {F : A → B → 𝒰 ℓf} {G : B → A → 𝒰 ℓg}
  {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
  {x : A} {y : B} (f : F x y) : 𝒰 (ℓg ⊔ ℓfg ⊔ ℓgf) where
  no-eta-equality
  constructor make-qinv
  field
    inv      : G y x
    inverses : Inverses f inv

  open Inverses inverses public

  op : quasi-inverse inv
  op .inv = f
  op .inverses .Inverses.inv-o = inv-i
  op .inverses .Inverses.inv-i = inv-o
{-# INLINE make-qinv #-}


module _
  {ℓa ℓb ℓf ℓg ℓfg ℓgf : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {F : A → B → 𝒰 ℓf} {G : B → A → 𝒰 ℓg}
  {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
  {x : A} {y : B} {f : F x y} where

  qinv : (g : G y x) → f retraction-of g → f section-of g
       → quasi-inverse f
  qinv g r s .quasi-inverse.inv = g
  qinv g r s .quasi-inverse.inverses .Inverses.inv-o = r
  qinv g r s .quasi-inverse.inverses .Inverses.inv-i = s
  {-# INLINE qinv #-}

  inverses→qinv : {g : G y x} → Inverses f g → quasi-inverse f
  inverses→qinv {g} i .quasi-inverse.inv = g
  inverses→qinv     i .quasi-inverse.inverses = i
  {-# INLINE inverses→qinv #-}

  qinv→has-section : quasi-inverse f → has-section f
  qinv→has-section i .section = i .quasi-inverse.inv
  qinv→has-section i .is-section = i .quasi-inverse.inverses .Inverses.inv-o
  {-# INLINE qinv→has-section #-}

module _
  {ℓa ℓf : Level} {A : 𝒰 ℓa} {F : A → A → 𝒰 ℓf}
  ⦃ _ : Refl F ⦄ ⦃ _ : Trans F ⦄ ⦃ _ : HUnit-o F ⦄ {x : A}  where

  id-qinv : quasi-inverse {x = x} refl
  id-qinv .quasi-inverse.inv = refl
  id-qinv .quasi-inverse.inverses .Inverses.inv-o = ∙-id-o refl
  id-qinv .quasi-inverse.inverses .Inverses.inv-i = ∙-id-o refl


instance
  Dual-Inverses
    : ∀ {ℓa ℓb ℓa∙ ℓb∙ ℓf ℓg} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
      {F : A → B → 𝒰 ℓf}  {G : B → A → 𝒰 ℓg}
      {U : A → A → 𝒰 ℓa∙} {V : B → B → 𝒰 ℓb∙}
      ⦃ _ : Comp F G U ⦄   ⦃ _ : Comp G F V ⦄
      ⦃ _ : Refl U ⦄       ⦃ _ : Refl V ⦄
      {x : A} {y : B}
    → Dual (Inverses {F = F} {G = G} {x = x} {y = y}) Inverses
  Dual-Inverses ._ᵒᵖ i .Inverses.inv-o = Inverses.inv-i i
  Dual-Inverses ._ᵒᵖ i .Inverses.inv-i = Inverses.inv-o i
