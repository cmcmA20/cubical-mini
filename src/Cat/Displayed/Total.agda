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
