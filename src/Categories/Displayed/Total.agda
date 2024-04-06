{-# OPTIONS --safe #-}
open import Categories.Displayed.Base
open import Categories.Prelude

module Categories.Displayed.Total {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where

import Categories.Morphism
import Categories.Displayed.Morphism as DM
import Categories.Displayed.Reasoning as DR

open Categories.Morphism B
open Displayed E
open DM E
open DR E

Total : Type (o ⊔ o′)
Total = Σ[ Carrier ꞉ Ob ] Ob[ Carrier ]

record Total-hom (X Y : Total) : Type (ℓ ⊔ ℓ′) where
  constructor total-hom
  field
    hom       : Hom (X .fst) (Y .fst)
    preserves : Hom[ hom ] (X .snd) (Y .snd)

open Total-hom

instance
  unquoteDecl H-Level-total-hom =
    declare-record-hlevel 2 H-Level-total-hom (quote Total-hom)

private variable
  X X′ Y Y′ : Total

total-hom-path : {f g : Total-hom X Y}
               → (p : f .hom ＝ g .hom)
               → f .preserves ＝[ p ] g .preserves
               → f ＝ g
total-hom-path p _  i .hom = p i
total-hom-path _ p′ i .preserves = p′ i

total-hom-pathp
  : {f : Total-hom X Y} {g : Total-hom X′ Y′}
  → (p : X ＝ X′) (q : Y ＝ Y′)
  → (r : ＜ f .hom ／ (λ i → Hom (p i .fst) (q i .fst)) ＼ g .hom ＞)
  → ＜ f .preserves ／ (λ z → Hom[ r z ] (p z .snd) (q z .snd)) ＼ g .preserves ＞
  → ＜ f ／ (λ i → Total-hom (p i) (q i)) ＼ g ＞
total-hom-pathp _ _ r _ i .hom = r i
total-hom-pathp _ _ _ s i .preserves = s i

∫ : Precategory (o ⊔ o′) (ℓ ⊔ ℓ′)
∫ .Precategory.Ob = Total
∫ .Precategory.Hom = Total-hom
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
    (ap hom $ ∫E._≅_.inv-l f)
    (ap hom $ ∫E._≅_.inv-r f)

total-iso→iso[] : ∀ {x y} → (f : x ∫E.≅ y) → x .snd ≅[ total-iso→iso f ] y .snd
total-iso→iso[] f = make-iso[ total-iso→iso f ]
    (∫E._≅_.to f .preserves)
    (∫E._≅_.from f .preserves)
    (ap preserves $ ∫E._≅_.inv-l f)
    (ap preserves $ ∫E._≅_.inv-r f)
