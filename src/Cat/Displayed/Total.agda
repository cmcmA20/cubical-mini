{-# OPTIONS --safe #-}
module Cat.Displayed.Total where

open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Morphism
import Cat.Displayed.Morphism as DM

module _ {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where
  open Cat.Morphism B
  open Displayed E
  open DM E

  Total : Type (o ⊔ o′)
  Total = Σ[ Carrier ꞉ Ob ] Ob[ Carrier ]

  Total-hom′ : (X Y : Total) → Type (ℓ ⊔ ℓ′)
  Total-hom′ X Y = Total-hom Hom Hom[_] (X .snd) (Y .snd)

  open Total-hom

  instance
    H-Level-Total-hom′
      : ∀ {X Y n}
        ⦃ _ : ∀ {x y} → H-Level n (Hom x y) ⦄
        ⦃ _ : ∀ {x y : Ob} {f : Hom x y} {x′ y′} → H-Level n (Hom[ f ] x′ y′) ⦄
      → H-Level n (Total-hom′ X Y)
    H-Level-Total-hom′ .H-Level.has-of-hlevel = ≅→is-of-hlevel _ Total-hom-Iso (hlevel _)
    {-# OVERLAPPING H-Level-Total-hom′ #-}

  private variable X X′ Y Y′ : Total

  ∫ : Precategory (o ⊔ o′) (ℓ ⊔ ℓ′)
  ∫ .Precategory.Ob = Total
  ∫ .Precategory.Hom = Total-hom′
  ∫ .Precategory.id .hom = id
  ∫ .Precategory.id .preserves = idᵈ
  ∫ .Precategory._∘_ f g .hom = f .hom ∘ g .hom
  ∫ .Precategory._∘_ f g .preserves = f .preserves ∘ᵈ g .preserves
  ∫ .Precategory.id-r _ = total-hom-path (id-r _) (id-rᵈ _)
  ∫ .Precategory.id-l _ = total-hom-path (id-l _) (id-lᵈ _)
  ∫ .Precategory.assoc _ _ _ = total-hom-path (assoc _ _ _) (assocᵈ _ _ _)

  πᶠ : Functor ∫ B
  πᶠ .Functor.F₀ = fst
  πᶠ .Functor.F₁ = Total-hom.hom
  πᶠ .Functor.F-id = refl
  πᶠ .Functor.F-∘ f g = refl

  private module ∫E = Cat.Morphism ∫

  private variable x y : ∫E.Ob

  open Iso

  total-iso→iso : x ≅ y → x .fst ≅ y .fst
  total-iso→iso f = iso
    (f .to .hom)
    (f .from .hom)
    (hom # f .inv-o)
    (hom # f .inv-i)

  total-iso→iso[] : ∀ {x y : ∫E.Ob} → (f : x ≅ y) → x .snd ≅[ total-iso→iso f ] y .snd
  total-iso→iso[] f = make-iso[ total-iso→iso f ]
    (f .to .preserves)
    (f .from .preserves)
    (preserves # f .inv-o)
    (preserves # f .inv-i)

  open Biinv

  total-equiv→equiv : x ≊ y → x .fst ≊ y .fst
  total-equiv→equiv f = biinv
    (f .to .hom)
    (f .from .hom)
    (hom # f .from-is-retraction)
    (f .section .hom)
    (hom # f .is-section)

  total-equiv→equiv[] : ∀ {x y : ∫E.Ob} → (f : x ≊ y) → x .snd ≊[ total-equiv→equiv f ] y .snd
  total-equiv→equiv[] f = make-equiv[ total-equiv→equiv f ]
    (f .to .preserves)
    (f .from .preserves)
    (preserves # f .from-is-retraction)
    (f .section .preserves)
    (preserves # f .is-section)

  open has-retraction[_]
  open has-section[_]

  is-biinv-fibrewise≃is-biinv-total
    : ∀ {x y : ∫E.Ob} {f : Hom (x .fst) (y .fst)} {f′ : Hom[ f ] (x .snd) (y .snd)}
    → Σ[ fbi ꞉ is-biinv f ] is-biinv[ fbi ] f′
    ≃ is-biinv {F = ∫E.Hom} (total-hom f f′)
  is-biinv-fibrewise≃is-biinv-total {x} {y} {f} {f′} = ≅ₜ→≃ $ iso one two re se where
    one : Σ[ fbi ꞉ is-biinv f ] is-biinv[ fbi ] f′ → is-biinv {F = ∫E.Hom} (total-hom f f′)
    one ((hr , hs) , hrᵈ , hsᵈ) = make-is-biinv
      (total-hom (hr .retraction) (hrᵈ .retractionᵈ))
      (total-hom-path (hr .is-retraction) (hrᵈ .is-retractionᵈ))
      (total-hom (hs .section) (hsᵈ .sectionᵈ))
      (total-hom-path (hs .is-section) (hsᵈ .is-sectionᵈ))
    two : is-biinv {F = ∫E.Hom} (total-hom f f′) → Σ[ fbi ꞉ is-biinv f ] is-biinv[ fbi ] f′
    two (hr , hs) .fst .fst = make-retraction (hr .retraction .hom) (ap hom $ hr .is-retraction)
    two (hr , hs) .fst .snd = make-section (hs .section .hom) (ap hom $ hs .is-section)
    two (hr , hs) .snd .fst = make-retraction[] (hr .retraction .preserves) (ap preserves $ hr .is-retraction)
    two (hr , hs) .snd .snd = make-section[] (hs .section .preserves) (ap preserves $ hs .is-section)

    re : one retraction-of two
    re i (hr , hs) .fst .retraction = hr .retraction
    re i (hr , hs) .fst .is-retraction = hr .is-retraction
    re i (hr , hs) .snd .section = hs .section
    re i (hr , hs) .snd .is-section = hs .is-section

    se : one section-of two
    se i ((hr , hs) , hrᵈ , hsᵈ) .fst .fst .retraction = hr .retraction
    se i ((hr , hs) , hrᵈ , hsᵈ) .fst .fst .is-retraction = hr .is-retraction
    se i ((hr , hs) , hrᵈ , hsᵈ) .fst .snd .section = hs .section
    se i ((hr , hs) , hrᵈ , hsᵈ) .fst .snd .is-section = hs .is-section
    se i ((hr , hs) , hrᵈ , hsᵈ) .snd .fst .retractionᵈ = hrᵈ .retractionᵈ
    se i ((hr , hs) , hrᵈ , hsᵈ) .snd .fst .is-retractionᵈ = hrᵈ .is-retractionᵈ
    se i ((hr , hs) , hrᵈ , hsᵈ) .snd .snd .sectionᵈ = hsᵈ .sectionᵈ
    se i ((hr , hs) , hrᵈ , hsᵈ) .snd .snd .is-sectionᵈ = hsᵈ .is-sectionᵈ

  is-biinv[]-is-prop
    : ∀ {x y : ∫E.Ob} {f : Hom (x .fst) (y .fst)} {f′ : Hom[ f ] (x .snd) (y .snd)}
    → (fbi : is-biinv f) → is-prop (is-biinv[ fbi ] f′)
  is-biinv[]-is-prop = base-is-prop+total-is-prop→fibres-are-prop (hlevel 1)
    (≃→is-of-hlevel 1 is-biinv-fibrewise≃is-biinv-total (hlevel 1))


module _ {o ℓ o′ ℓ′} {B : Precategory o ℓ} {E : Displayed B o′ ℓ′} where
  open Precategory B
  open Displayed E
  open DM E
  open Biinv

  instance
    H-Level-biinv[]
      : ∀ {n} {a b : Ob} {a′ : Ob[ a ]} {b′ : Ob[ b ]}
        {f : Hom a b} {f′ : Hom[ f ] a′ b′}
      → {fbi : is-biinv f} ⦃ _ : n ≥ʰ 1 ⦄ → H-Level n (is-biinv[ fbi ] f′)
    H-Level-biinv[] ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (is-biinv[]-is-prop E _)

  instance
    Extensional-≊[]
      : ∀ {ℓr} {a b : Ob} {a′ : Ob[ a ]} {b′ : Ob[ b ]} {f : a ≊ b}
      → ⦃ sa : Extensional (Hom[ f .to ] a′ b′) ℓr ⦄
      → Extensional (a′ ≊[ f ] b′) ℓr
    Extensional-≊[] {f} ⦃ sa ⦄ = ↪→extensional (≃→↪ (≅ₜ→≃ ≊[]-Iso))
      (Σ-prop→extensional! sa)
