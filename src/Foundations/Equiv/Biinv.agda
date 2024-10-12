{-# OPTIONS --safe #-}
module Foundations.Equiv.Biinv where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.Isomorphism
open import Foundations.Path.Base

private variable ℓ ℓ′ : Level

Biinvₜ : 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)
Biinvₜ = Biinv Fun Fun

instance
  ≊-Fun : ≊-notation (𝒰 ℓ) (𝒰 ℓ′) (𝒰 (ℓ ⊔ ℓ′))
  ≊-Fun ._≊_ = Biinvₜ

module _
  {ℓa ℓa∙ ℓb ℓb∙ ℓf ℓf⁻ : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {A∙ : A → A → 𝒰 ℓa∙} {B∙ : B → B → 𝒰 ℓb∙}
  {F : A → B → 𝒰 ℓf} {F⁻ : B → A → 𝒰 ℓf⁻}
  ⦃ _ : Refl A∙ ⦄ ⦃ _ : Refl B∙ ⦄
  ⦃ _ : Comp F F⁻ A∙ ⦄ ⦃ _ : Comp F⁻ F B∙ ⦄
  ⦃ _ : Comp F⁻ A∙ F⁻ ⦄ ⦃ _ : Comp B∙ F⁻ F⁻ ⦄
  ⦃ _ : GUnit-i F⁻ A∙ ⦄ ⦃ _ : GUnit-o B∙ F⁻ ⦄
  ⦃ _ : GAssoc F⁻ F F⁻ B∙ A∙ F⁻ ⦄
  {x : A} {y : B} where

  is-biinv→section-is-retraction : {f : F x y} ((hr , hs) : is-biinv f) → f ∙ hs .section ＝ refl
  is-biinv→section-is-retraction {f} (hr , hs) =
      f ∙ g            ~⟨ f ◁ ∙-id-i _ ⟨
      f ∙ g ∙ refl     ~⟨ f ◁ g ◁ hr .is-retraction ⟨
      f ∙ g ∙ f ∙ h    ~⟨ f ◁ ∙-assoc _ _ _ ⟩
      f ∙ (g ∙ f) ∙ h  ~⟨ f ◁ hs .is-section ▷ h ⟩
      f ∙ refl ∙ h     ~⟨ f ◁ ∙-id-o _ ⟩
      f ∙ h            ~⟨ hr .is-retraction ⟩
      _                ∎
      where
      g = hs .section
      h = hr .retraction

  is-biinv→qinv : {f : F x y} → is-biinv f → quasi-inverse f
  is-biinv→qinv {f} (hr , hs) = qinv (hs .section) (hs .is-section) (is-biinv→section-is-retraction (hr , hs))

  ≊→≅ : Biinv F F⁻ x y → Iso F F⁻ x y
  ≊→≅ e = qinv→≅ (e .fst) (is-biinv→qinv (e .snd))

module _
  {ℓa ℓa∙ ℓb ℓb∙ ℓf ℓf⁻ : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {A∙ : A → A → 𝒰 ℓa∙} {B∙ : B → B → 𝒰 ℓb∙}
  {F : A → B → 𝒰 ℓf} {F⁻ : B → A → 𝒰 ℓf⁻}
  ⦃ _ : Refl A∙ ⦄ ⦃ _ : Refl B∙ ⦄
  ⦃ _ : Comp F F⁻ A∙ ⦄ ⦃ _ : Comp F⁻ F B∙ ⦄
  ⦃ _ : Comp B∙ B∙ B∙ ⦄ ⦃ _ : Comp A∙ F F ⦄ ⦃ _ : Comp F B∙ F ⦄
  ⦃ _ : GUnit-o B∙ B∙ ⦄ ⦃ _ : GUnit-o A∙ F ⦄
  ⦃ _ : GAssoc F⁻ F B∙ B∙ F B∙ ⦄
  ⦃ _ : GAssoc F F⁻ F A∙ B∙ F ⦄ where

  is-biinv→retraction-is-section : ∀ {x y} {f : F x y} ((hr , hs) : is-biinv f) → hr .retraction ∙ f ＝ refl
  is-biinv→retraction-is-section {f} (hr , hs) =
    h ∙ f            ~⟨ ∙-id-o _ ⟨
    refl ∙ h ∙ f     ~⟨ hs .is-section ▷ h ∙ f ⟨
    (g ∙ f) ∙ h ∙ f  ~⟨ ∙-assoc _ _ _ ⟨
    g ∙ f ∙ h ∙ f    ~⟨ g ◁ ∙-assoc _ _ _ ⟩
    g ∙ (f ∙ h) ∙ f  ~⟨ g ◁ hr .is-retraction ▷ f ⟩
    g ∙ refl ∙ f     ~⟨ g ◁ ∙-id-o _ ⟩
    g ∙ f            ~⟨ hs .is-section ⟩
    _                ∎
    where
    g = hs .section
    h = hr .retraction

  instance
    Dual-≊ : Dual (Biinv F F⁻) (Biinv F⁻ F)
    Dual-≊ ._ᵒᵖ (_ , hr , _ ) .fst = hr .retraction
    Dual-≊ ._ᵒᵖ (f , hr , hs) .snd .fst .retraction = f
    Dual-≊ ._ᵒᵖ (f , hr , hs) .snd .fst .is-retraction = is-biinv→retraction-is-section (hr , hs)
    Dual-≊ ._ᵒᵖ (f , hr , hs) .snd .snd .section = f
    Dual-≊ ._ᵒᵖ (f , hr , hs) .snd .snd .is-section = hr .is-retraction

is-biinv→is-equiv : ∀{ℓa ℓb} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {f : A → B} → is-biinv f → is-equiv f
is-biinv→is-equiv bf = qinv→is-equiv (is-biinv→qinv bf)

module _
  {ℓa ℓa∙ ℓb ℓb∙ ℓc ℓc∙ ℓf ℓf⁻ ℓg ℓfg : Level}
  {A : 𝒰 ℓa} {B : 𝒰 ℓb} {C : 𝒰 ℓc}
  {A∙ : A → A → 𝒰 ℓa∙} {B∙ : B → B → 𝒰 ℓb∙} {C∙ : C → C → 𝒰 ℓc∙}
  {F : A → B → 𝒰 ℓf} {F⁻ : B → A → 𝒰 ℓf⁻}
  ⦃ _ : Refl A∙ ⦄ ⦃ _ : Refl B∙ ⦄
  ⦃ _ : Comp B∙ B∙ B∙ ⦄ ⦃ _ : Comp A∙ F F ⦄ ⦃ _ : Comp F B∙ F ⦄
  ⦃ _ : GUnit-o B∙ B∙ ⦄ ⦃ _ : GUnit-o A∙ F ⦄
  ⦃ _ : Comp F⁻ F B∙ ⦄ ⦃ _ : GAssoc F⁻ F B∙ B∙ F B∙ ⦄
  ⦃ _ : Comp F F⁻ A∙ ⦄ ⦃ _ : GAssoc F F⁻ F A∙ B∙ F ⦄
  {x : A} {y : B} {z : C} where

  module _
    {G : C → A → 𝒰 ℓg}
    {G∙F : C → B → 𝒰 ℓfg}
    ⦃ _ : Comp G F G∙F ⦄ ⦃ _ : Comp G∙F F⁻ G ⦄
    ⦃ _ : Comp G∙F B∙ G∙F ⦄ ⦃ _ : GUnit-i G∙F B∙ ⦄ ⦃ _ : GAssoc G∙F F⁻ F G B∙ G∙F ⦄
    ⦃ _ : Comp G A∙ G ⦄ ⦃ _ : GUnit-i G A∙ ⦄ ⦃ _ : GAssoc G F F⁻ G∙F A∙ G ⦄ where

      is-biinv→pre-is-equiv : {f : F x y} → is-biinv f → is-equiv {A = G z x} (_∙ f)
      is-biinv→pre-is-equiv {f} (hr , hs) = qinv→is-equiv $ qinv
        (_∙ hr .retraction)
        (fun-ext λ gf → sym (∙-assoc gf _ f) ∙ (gf ◁ is-biinv→retraction-is-section (hr , hs)) ∙ ∙-id-i _)
        (fun-ext λ g  → sym (∙-assoc g f _) ∙ (g ◁ hr .is-retraction) ∙ ∙-id-i _)

  module _
    {G : B → C → 𝒰 ℓg}
    {F∙G : A → C → 𝒰 ℓfg}
    ⦃ _ : Comp F G F∙G ⦄ ⦃ _ : Comp F⁻ F∙G G ⦄
    ⦃ _ : Comp A∙ F∙G F∙G ⦄ ⦃ _ : GUnit-o A∙ F∙G ⦄ ⦃ _ : GAssoc F F⁻ F∙G A∙ G F∙G ⦄
    ⦃ _ : Comp B∙ G G ⦄ ⦃ _ : GUnit-o B∙ G ⦄ ⦃ _ : GAssoc F⁻ F G B∙ F∙G G ⦄ where

      is-biinv→post-is-equiv : {f : F x y} → is-biinv f → is-equiv {A = G y z} (f ∙_)
      is-biinv→post-is-equiv {f} (hr , hs) = qinv→is-equiv $ qinv
        (hr .retraction ∙_)
        (fun-ext λ fg → ∙-assoc f _ fg ∙ (hr .is-retraction ▷ fg) ∙ ∙-id-o fg)
        (fun-ext λ g  → ∙-assoc _ f g ∙ (is-biinv→retraction-is-section (hr , hs) ▷ g) ∙ ∙-id-o g)
