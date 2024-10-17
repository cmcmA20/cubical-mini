{-# OPTIONS --safe #-}
module Functions.Equiv.Biinv where

open import Meta.Prelude
open import Meta.Extensionality
open import Meta.Record

module _
  {ℓa ℓa∙ ℓb ℓb∙ ℓh : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {A∙ : A → A → 𝒰 ℓa∙} {B∙ : B → B → 𝒰 ℓb∙}
  {F : A → B → 𝒰 ℓh} {F⁻ : B → A → 𝒰 ℓh}
  ⦃ _ : Refl A∙ ⦄ ⦃ _ : Refl B∙ ⦄
  ⦃ _ : Comp F F⁻ A∙ ⦄ ⦃ _ : Comp F⁻ F B∙ ⦄
  ⦃ _ : Comp F⁻ A∙ F⁻ ⦄ ⦃ _ : Comp B∙ F⁻ F⁻ ⦄
  ⦃ _ : Comp A∙ A∙ A∙ ⦄ ⦃ _ : Comp B∙ B∙ B∙ ⦄
  ⦃ _ : GUnit-o A∙ A∙ ⦄ ⦃ _ : GUnit-i B∙ B∙ ⦄
  ⦃ _ : GUnit-i F⁻ A∙ ⦄ ⦃ _ : GUnit-o B∙ F⁻ ⦄
  ⦃ _ : GAssoc F F⁻ A∙ A∙ F⁻ A∙ ⦄ ⦃ _ : GAssoc F⁻ F F⁻ B∙ A∙ F⁻ ⦄
  ⦃ _ : GAssoc B∙ F⁻ F F⁻ B∙ B∙ ⦄

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

  open Biinv
  instance
    H-Level-is-biinv : ∀{n} ⦃ _ : n ≥ʰ 1 ⦄ {f : F x y} → H-Level n (is-biinv f)
    H-Level-is-biinv ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-biinv-is-prop

  opaque
    private
      ≊-inverse-unique-internal
        : (x′ : A) (p : x ＝ x′) (y′ : B) (q : y ＝ y′)
          {e : Biinv F F⁻ x y} {e′ : Biinv F F⁻ x′ y′}
        → ＜ e .to ／ (λ i → F (p i) (q i)) ＼ e′ .to ＞
        → ＜ e .from ／ (λ i → F⁻ (q i) (p i)) ＼ e′ .from ＞
      ≊-inverse-unique-internal = J>! (J>! λ {e e′} r
        → sym (∙-id-o _)
        ∙ (sym ((is-biinv→unique-inverse (e′ .has-biinv) ▷ e′ .to) ∙ e′ .is-section) ▷ e .from)
        ∙ sym (∙-assoc _ (e′ .to) _)
        ∙ (e′ .from ◁ sym r ▷ e .from)
        ∙ (e′ .from ◁ e .from-is-retraction)
        ∙ ∙-id-i _ )

    ≊-inverse-unique
      : {x′ : A} (p : x ＝ x′) {y′ : B} (q : y ＝ y′)
        {e : Biinv F F⁻ x y} {e′ : Biinv F F⁻ x′ y′}
      → ＜ e .to ／ (λ i → F (p i) (q i)) ＼ e′ .to ＞
      → ＜ e .from ／ (λ i → F⁻ (q i) (p i)) ＼ e′ .from ＞
    ≊-inverse-unique p = ≊-inverse-unique-internal _ p _

  private
    ≊-pathᴾ-internal
      : ∀ {x′ y′} (p : x ＝ x′) (q : y ＝ y′)
      → {e : Biinv F F⁻ x y} {e′ : Biinv F F⁻ x′ y′}
      → (r : ＜ e .to ／ (λ i → F (p i) (q i)) ＼ e′ .to ＞)
      → ＜ e .has-biinv ／ (λ i → is-biinv (r i)) ＼ e′ .has-biinv ＞
      → ＜ e ／ (λ i → Biinv F F⁻ (p i) (q i)) ＼ e′ ＞
    ≊-pathᴾ-internal _ _ r _ i .to = r i
    ≊-pathᴾ-internal _ _ _ s i .has-biinv = s i

  ≊-pathᴾ
    : ∀ {x′ y′} (p : x ＝ x′) (q : y ＝ y′)
      {e : Biinv F F⁻ x y} {e′ : Biinv F F⁻ x′ y′}
    → ＜ e .to ／ (λ i → F (p i) (q i)) ＼ e′ .to ＞
    → ＜ e ／ (λ i → Biinv F F⁻ (p i) (q i)) ＼ e′ ＞
  ≊-pathᴾ p q r = ≊-pathᴾ-internal p q r prop!

  -- TODO later
  -- ≊-pathᴾ-from
  --   : ∀ {x′ y′} (p : x ＝ x′) (q : y ＝ y′)
  --     {e : Biinv F F⁻ x y} {e′ : Biinv F F⁻ x′ y′}
  --   → ＜ e .from ／ (λ i → F⁻ (q i) (p i)) ＼ e′ .from ＞
  --   → ＜ e ／ (λ i → Biinv F F⁻ (p i) (q i)) ＼ e′ ＞
  -- ≊-pathᴾ-from p q {e} {e′} r = ?

  -- ≊-path-from : {e e′ : Biinv F F⁻ x y} → e .from ＝ e′ .from → e ＝ e′
  -- ≊-path-from = ≊-pathᴾ-from refl refl

  instance
    Extensional-≊ : ∀ {ℓr} ⦃ sa : Extensional (F x y) ℓr ⦄ → Extensional (Biinv F F⁻ x y) ℓr
    Extensional-≊ ⦃ sa ⦄ .Pathᵉ e₁ e₂ = sa .Pathᵉ (e₁ .to) (e₂ .to)
    Extensional-≊ ⦃ sa ⦄ .reflᵉ e = sa .reflᵉ (e .to)
    Extensional-≊ ⦃ sa ⦄ .idsᵉ .to-path p = ≊-pathᴾ refl refl (sa .idsᵉ .to-path p)
    Extensional-≊ ⦃ sa ⦄ .idsᵉ .to-path-over p = sa .idsᵉ .to-path-over p
