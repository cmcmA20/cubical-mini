{-# OPTIONS --safe #-}
module Categories.Displayed.Total where

open import Categories.Displayed.Base
open import Categories.Prelude

import Categories.Morphism
import Categories.Displayed.Morphism as DM
import Categories.Displayed.Reasoning as DR

module _ {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where
  open Categories.Morphism B
  open Displayed E
  open DM E
  open DR E

  Total : Type (o ⊔ o′)
  Total = Σ[ Carrier ꞉ Ob ] Ob[ Carrier ]

  Total-hom′ : (X Y : Total) → Type (ℓ ⊔ ℓ′)
  Total-hom′ X Y = Total-hom Hom Hom[_] (X .snd) (Y .snd)

  open Total-hom

  instance
    H-Level-Total-hom′ : ∀ {X Y n} ⦃ _ : n ≥ʰ 2 ⦄ → H-Level n (Total-hom′ X Y)
    H-Level-Total-hom′ ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 (≅→is-of-hlevel! 2 Total-hom-Iso)

  private variable X X′ Y Y′ : Total

  ∫ : Precategory (o ⊔ o′) (ℓ ⊔ ℓ′)
  ∫ .Precategory.Ob = Total
  ∫ .Precategory.Hom = Total-hom′
  ∫ .Precategory.Hom-set = hlevel!
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

  private module ∫E = Categories.Morphism ∫

  private variable x y : ∫E.Ob

  total-iso→iso : x ∫E.≅ y → x .fst ≅ y .fst
  total-iso→iso f = make-iso
      (∫E._≅_.to f .hom)
      (∫E._≅_.from f .hom)
      (hom $ ∫E._≅_.inv-l f)
      (hom $ ∫E._≅_.inv-r f)

  total-iso→iso[] : ∀ {x y} → (f : x ∫E.≅ y) → x .snd ≅[ total-iso→iso f ] y .snd
  total-iso→iso[] f = make-iso[ total-iso→iso f ]
      (∫E._≅_.to f .preserves)
      (∫E._≅_.from f .preserves)
      (preserves $ ∫E._≅_.inv-l f)
      (preserves $ ∫E._≅_.inv-r f)
