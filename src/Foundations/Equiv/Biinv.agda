{-# OPTIONS --safe #-}
module Foundations.Equiv.Biinv where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.Isomorphism
open import Foundations.Path.Base

Biinvₜ : ∀ {ℓ ℓ′} → 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)
Biinvₜ = Biinv Fun Fun

instance
  ≊-Fun : ∀ {ℓ ℓ′} → ≊-notation (𝒰 ℓ) (𝒰 ℓ′) (𝒰 (ℓ ⊔ ℓ′))
  ≊-Fun ._≊_ = Biinvₜ

open Biinv

module _
  {ℓa ℓa∙ ℓb ℓb∙ ℓh : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {A∙ : A → A → 𝒰 ℓa∙} {B∙ : B → B → 𝒰 ℓb∙}
  {F : A → B → 𝒰 ℓh} {F⁻ : B → A → 𝒰 ℓh}
  ⦃ _ : Refl A∙ ⦄ ⦃ _ : Refl B∙ ⦄
  ⦃ _ : Comp F F⁻ A∙ ⦄ ⦃ _ : Comp F⁻ F B∙ ⦄
  ⦃ _ : Comp B∙ F⁻ F⁻ ⦄ ⦃ _ : Comp F⁻ A∙ F⁻ ⦄
  ⦃ _ : GUnit-o B∙ F⁻ ⦄ ⦃ _ : GUnit-i F⁻ A∙ ⦄
  ⦃ _ : GAssoc F⁻ F F⁻ B∙ A∙ F⁻ ⦄ where

  opaque
    is-biinv→unique-inverse
      : {x : A} {y : B} {f : F x y} ((hr , hs) : is-biinv f)
      → hr .retraction ＝ hs .section
    is-biinv→unique-inverse {x} {y} {f} (hr , hs) =
        h            ~⟨ (hs .is-section ▷ h) ∙ ∙-id-o h ⟨
        (g ∙ f) ∙ h  ~⟨ ∙-assoc g f h ⟨
        g ∙ (f ∙ h)  ~⟨ (g ◁ hr .is-retraction) ∙ ∙-id-i g ⟩
        g            ∎
        where
        g : F⁻ y x
        g = hs .section
        h : F⁻ y x
        h = hr .retraction

  is-biinv→qinv
    : {x : A} {y : B} {f : F x y}
    → is-biinv f → quasi-inverse f
  is-biinv→qinv {f} (hr , hs) = qinv (hr .retraction)
    ((is-biinv→unique-inverse (hr , hs) ▷ f) ∙ hs .is-section)
    (hr .is-retraction)
  {-# INLINE is-biinv→qinv #-}

  ≊→≅ : {x : A} {y : B} → Biinv F F⁻ x y → Iso F F⁻ x y
  ≊→≅ e = qinv→≅ (e .to) (is-biinv→qinv (e .has-biinv))

  instance
    Dual-≊ : Dual (Biinv F F⁻) (Biinv F⁻ F)
    Dual-≊ ._ᵒᵖ e .to = e .from
    Dual-≊ ._ᵒᵖ e .has-biinv = make-is-biinv (e .to)
      ((is-biinv→unique-inverse (e .has-biinv) ▷ e .to) ∙ e .is-section)
      (e .to) (e .from-is-retraction)

is-biinv→is-equiv : ∀{ℓa ℓb} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {f : A → B} → is-biinv f → is-equiv f
is-biinv→is-equiv bf = qinv→is-equiv (is-biinv→qinv bf)
{-# INLINE is-biinv→is-equiv #-}


module _
  {ℓa ℓa∙ ℓb ℓb∙ ℓc ℓc∙ ℓab ℓac ℓbc : Level}
  {A : 𝒰 ℓa} {B : 𝒰 ℓb} {C : 𝒰 ℓc}
  {A∙ : A → A → 𝒰 ℓa∙} {B∙ : B → B → 𝒰 ℓb∙} {C∙ : C → C → 𝒰 ℓc∙}
  {F : A → B → 𝒰 ℓab} {F⁻ : B → A → 𝒰 ℓab}
  ⦃ _ : Refl A∙ ⦄ ⦃ _ : Refl B∙ ⦄
  ⦃ _ : Comp F F⁻ A∙ ⦄ ⦃ _ : Comp F⁻ F B∙ ⦄
  ⦃ _ : Comp B∙ F⁻ F⁻ ⦄ ⦃ _ : Comp F⁻ A∙ F⁻ ⦄
  ⦃ _ : GUnit-o B∙ F⁻ ⦄ ⦃ _ : GUnit-i F⁻ A∙ ⦄
  ⦃ _ : GAssoc F⁻ F F⁻ B∙ A∙ F⁻ ⦄
  {x : A} {y : B} {z : C} where

  module _
    {G : C → A → 𝒰 ℓac} {G∙F : C → B → 𝒰 ℓbc}
    ⦃ _ : Comp G F G∙F ⦄ ⦃ _ : Comp G∙F F⁻ G ⦄
    ⦃ _ : Comp G∙F B∙ G∙F ⦄ ⦃ _ : Comp G A∙ G ⦄
    ⦃ _ : GUnit-i G∙F B∙ ⦄ ⦃ _ : GUnit-i G A∙ ⦄
    ⦃ _ : GAssoc G F F⁻ G∙F A∙ G ⦄ ⦃ _ : GAssoc G∙F F⁻ F G B∙ G∙F ⦄ where

      is-biinv→pre-is-equiv : {f : F x y} → is-biinv f → is-equiv {A = G z x} (_∙ f)
      is-biinv→pre-is-equiv {f} (hr , hs) = qinv→is-equiv $ qinv
        (_∙ hr .retraction)
        (fun-ext λ gf → sym (∙-assoc gf _ f) ∙ (gf ◁ (is-biinv→unique-inverse (hr , hs) ▷ f) ∙ hs .is-section) ∙ ∙-id-i _)
        (fun-ext λ g  → sym (∙-assoc g f _) ∙ (g ◁ hr .is-retraction) ∙ ∙-id-i _)

  module _
    {G : B → C → 𝒰 ℓbc} {F∙G : A → C → 𝒰 ℓac}
    ⦃ _ : Comp F G F∙G ⦄ ⦃ _ : Comp F⁻ F∙G G ⦄
    ⦃ _ : Comp A∙ F∙G F∙G ⦄ ⦃ _ : Comp B∙ G G ⦄
    ⦃ _ : GUnit-o A∙ F∙G ⦄ ⦃ _ : GUnit-o B∙ G ⦄
    ⦃ _ : GAssoc F F⁻ F∙G A∙ G F∙G ⦄ ⦃ _ : GAssoc F⁻ F G B∙ F∙G G ⦄ where

      is-biinv→post-is-equiv : {f : F x y} → is-biinv f → is-equiv {A = G y z} (f ∙_)
      is-biinv→post-is-equiv {f} (hr , hs) = qinv→is-equiv $ qinv
        (hr .retraction ∙_)
        (fun-ext λ fg → ∙-assoc f _ fg ∙ (hr .is-retraction ▷ fg) ∙ ∙-id-o fg)
        (fun-ext λ g  → ∙-assoc _ f g ∙ ((is-biinv→unique-inverse (hr , hs) ▷ f) ∙ hs .is-section ▷ g) ∙ ∙-id-o g)
