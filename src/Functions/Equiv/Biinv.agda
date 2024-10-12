{-# OPTIONS --safe #-}
module Functions.Equiv.Biinv where

open import Meta.Prelude
open import Meta.Record

module _
  {ℓa ℓa∙ ℓb ℓb∙ ℓf ℓf⁻ : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {A∙ : A → A → 𝒰 ℓa∙} {B∙ : B → B → 𝒰 ℓb∙}
  {F : A → B → 𝒰 ℓf} {F⁻ : B → A → 𝒰 ℓf⁻}
  ⦃ _ : Refl A∙ ⦄ ⦃ _ : Refl B∙ ⦄
  ⦃ _ : Comp F F⁻ A∙ ⦄ ⦃ _ : Comp F⁻ F B∙ ⦄

  ⦃ _ : Comp B∙ B∙ B∙ ⦄ ⦃ _ : Comp A∙ F F ⦄ ⦃ _ : Comp F B∙ F ⦄
  ⦃ _ : Comp F⁻ A∙ F⁻ ⦄ ⦃ _ : Comp A∙ A∙ A∙ ⦄ ⦃ _ : Comp B∙ F⁻ F⁻ ⦄
  ⦃ _ : GUnit-o B∙ B∙ ⦄ ⦃ _ : GUnit-o A∙ F ⦄ ⦃ _ : GUnit-o A∙ A∙ ⦄ ⦃ _ : GUnit-o B∙ F⁻ ⦄
  ⦃ _ : GAssoc F⁻ F B∙ B∙ F B∙ ⦄ ⦃ _ : GAssoc F F⁻ F A∙ B∙ F ⦄
  ⦃ _ : GAssoc F F⁻ A∙ A∙ F⁻ A∙ ⦄ ⦃ _ : GAssoc F⁻ F F⁻ B∙ A∙ F⁻ ⦄

  ⦃ _ : GUnit-i B∙ B∙ ⦄ ⦃ _ : GUnit-i F⁻ A∙ ⦄ ⦃ _ : GAssoc B∙ F⁻ F F⁻ B∙ B∙ ⦄
  {x : A} {y : B}
  where
  qinv→has-retraction-is-contr
    : {f : F x y} → quasi-inverse f → is-contr (has-retraction f)
  qinv→has-retraction-is-contr fi = ≅→is-of-hlevel 0 has-retraction-Iso $
    is-biinv→post-is-equiv {C∙ = A∙} (qinv→is-biinv fi) .equiv-proof refl

  qinv→has-section-is-contr
    : {f : F x y} → quasi-inverse f → is-contr (has-section f)
  qinv→has-section-is-contr fi = ≅→is-of-hlevel 0 has-section-Iso $
    is-biinv→pre-is-equiv {C∙ = B∙} (qinv→is-biinv fi) .equiv-proof refl

  is-biinv-is-prop : {f : F x y} → is-prop (is-biinv f)
  is-biinv-is-prop {f} = contractible-if-inhabited contract where
    contract : is-biinv f → is-contr (is-biinv f)
    contract ibiinv =
      ×-is-of-hlevel 0 (qinv→has-retraction-is-contr i)
                       (qinv→has-section-is-contr i)
      where i = is-biinv→qinv ibiinv

  instance
    H-Level-is-biinv : ∀{n} ⦃ _ : n ≥ʰ 1 ⦄ {f : F x y} → H-Level n (is-biinv f)
    H-Level-is-biinv ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-biinv-is-prop
