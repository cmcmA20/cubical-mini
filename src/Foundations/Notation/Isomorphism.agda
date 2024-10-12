{-# OPTIONS --safe #-}
module Foundations.Notation.Isomorphism where

open import Foundations.Prim.Type

open import Foundations.Notation.Composition
open import Foundations.Notation.Duality
open import Foundations.Notation.Invertibility.Quasi
open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Retraction
open import Foundations.Notation.Section
open import Foundations.Notation.Underlying
open import Foundations.Notation.Unital.Outer

open import Agda.Builtin.Sigma

module _
  {ℓa ℓb ℓf ℓg ℓfg ℓgf : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  (F : A → B → 𝒰 ℓf) (G : B → A → 𝒰 ℓg)
  {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄ where

  record Iso (x : A) (y : B) : 𝒰 (ℓf ⊔ ℓg ⊔ ℓfg ⊔ ℓgf) where
    no-eta-equality
    constructor make-iso
    field
      to       : F x y
      from     : G y x
      inverses : Inverses to from

    open Inverses inverses public
  {-# INLINE make-iso #-}

open Iso

module _
  {ℓa ℓb ℓf ℓg ℓfg ℓgf : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {F : A → B → 𝒰 ℓf} {G : B → A → 𝒰 ℓg}
  {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
  {x : A} {y : B} where

  iso : (f : F x y) (g : G y x) → f retraction-of g → f section-of g
      → Iso F G x y
  iso f g r s .to = f
  iso f g r s .from = g
  iso f g r s .inverses .Inverses.inv-o = r
  iso f g r s .inverses .Inverses.inv-i = s
  {-# INLINE iso #-}

  qinv→≅ : (f : F x y) (fi : quasi-inverse f) → Iso F G x y
  qinv→≅ f fi .to = f
  qinv→≅ f fi .from = fi .quasi-inverse.inv
  qinv→≅ f fi .inverses = fi .quasi-inverse.inverses
  {-# INLINE qinv→≅ #-}

  ≅→qinv : (i : Iso F G x y) → quasi-inverse (i .to)
  ≅→qinv i .quasi-inverse.inv = i .from
  ≅→qinv i .quasi-inverse.inverses = i .inverses
  {-# INLINE ≅→qinv #-}

  ≅→to-has-section : (i : Iso F G x y) → has-section (i .to)
  ≅→to-has-section i .section = i .from
  ≅→to-has-section i .is-section = i .inv-o
  {-# INLINE ≅→to-has-section #-}

  ≅→from-has-section : (i : Iso F G x y) → has-section (i .from)
  ≅→from-has-section i .section = i .to
  ≅→from-has-section i .is-section = i .inv-i
  {-# INLINE ≅→from-has-section #-}

  ≅→to-has-retraction : (i : Iso F G x y) → has-retraction (i .to)
  ≅→to-has-retraction i .retraction = i .from
  ≅→to-has-retraction i .is-retraction = i .inv-i
  {-# INLINE ≅→to-has-retraction #-}

  ≅→from-has-retraction : (i : Iso F G x y) → has-retraction (i .from)
  ≅→from-has-retraction i .retraction = i .to
  ≅→from-has-retraction i .is-retraction = i .inv-o
  {-# INLINE ≅→from-has-retraction #-}

  qinv→retract : (f : F x y) → quasi-inverse f → Retract G x y
  qinv→retract _ fi .fst = fi .quasi-inverse.inv
  qinv→retract f _ .snd .section = f
  qinv→retract _ fi .snd .is-section = fi .quasi-inverse.inverses .Inverses.inv-i
  {-# INLINE qinv→retract #-}

  qinv→retract⁻ : (f : F x y) → quasi-inverse f → Retract F y x
  qinv→retract⁻ f _ .fst = f
  qinv→retract⁻ _ fi .snd .section = fi .quasi-inverse.inv
  qinv→retract⁻ _ fi .snd .is-section = fi .quasi-inverse.inverses .Inverses.inv-o
  {-# INLINE qinv→retract⁻ #-}

  ≅→retract : Iso F G x y → Retract F y x
  ≅→retract i .fst = i .to
  ≅→retract i .snd = ≅→to-has-section i
  {-# INLINE ≅→retract #-}

-- homogeneous isomorphism
HIso
  : ∀ {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) ⦃ _ : Refl R ⦄ ⦃ _ : Trans R ⦄
  → (x y : A) → 𝒰 ℓ
HIso R = Iso R R


record ≅-notation {ℓa ℓb ℓ}
  (A : 𝒰 ℓa) (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰ω where
  infix 1 _≅_
  field _≅_ : A → B → R
open ≅-notation ⦃ ... ⦄ public
{-# DISPLAY ≅-notation._≅_ _ a b = a ≅ b #-}


instance
  Funlike-≅
    : {ℓa ℓb ℓc ℓf ℓg ℓfg ℓgf : Level}
      {A : 𝒰 ℓa} {B : 𝒰 ℓb} ⦃ ua : Underlying A ⦄
      {F : A → B → 𝒰 ℓf} {G : B → A → 𝒰 ℓg}
      {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
      {x : A} {y : B} {C : Σ (F x y) (λ _ → ⌞ x ⌟) → 𝒰 ℓc}
      ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
      ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
      ⦃ f : Funlike ur (F x y) ⌞ x ⌟ C ⦄
    → Funlike ur (Iso F G x y) ⌞ x ⌟ λ (i , a) → C (i .to , a)
  Funlike-≅ ._#_ i a = i .to # a

  Refl-≅
    : ∀ {ℓa ℓ} {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ}
      ⦃ _ : Refl R ⦄ ⦃ _ : Trans R ⦄ ⦃ _ : HUnit-o R ⦄
    → Refl (Iso R R)
  Refl-≅ .refl .to = refl
  Refl-≅ .refl .from = refl
  Refl-≅ .refl .inverses .Inverses.inv-o = ∙-id-o _
  Refl-≅ .refl .inverses .Inverses.inv-i = ∙-id-o _

  Dual-≅
    : ∀ {ℓa ℓb ℓa∙ ℓb∙ ℓf ℓg} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
      {F : A → B → 𝒰 ℓf}  {G : B → A → 𝒰 ℓg}
      {U : A → A → 𝒰 ℓa∙} {V : B → B → 𝒰 ℓb∙}
      ⦃ _ : Comp F G U ⦄   ⦃ _ : Comp G F V ⦄
      ⦃ _ : Refl U ⦄       ⦃ _ : Refl V ⦄
    → Dual (Iso F G) (Iso G F)
  Dual-≅ ._ᵒᵖ i .to = i .from
  Dual-≅ ._ᵒᵖ i .from = i .to
  Dual-≅ ._ᵒᵖ i .inverses = i .inverses ᵒᵖ
