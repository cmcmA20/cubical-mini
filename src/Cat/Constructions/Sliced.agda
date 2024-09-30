{-# OPTIONS --safe #-}
open import Cat.Prelude

module Cat.Constructions.Sliced {o h} (C : Precategory o h)
  ⦃ hl : ∀ {x y} → H-Level 2 (Precategory.Hom C x y) ⦄ where

open import Cat.Constructions.Slice C
import Cat.Morphism

open Precategory C
module C↓c {c} = Cat.Morphism (Slice c)

private variable c : Ob

record _⇑_ {ℓ} (T : Pred Ob ℓ) (c : Ob) : 𝒰 (ℓ ⊔ o ⊔ h) where
  constructor _↑_
  field
    {support} : Ob
    thing     : T support
    thinning  : support ⇒ c

unquoteDecl sliced-iso = declare-record-iso sliced-iso (quote _⇑_)

private variable
  ℓ : Level
  T : Pred Ob ℓ

open /-Obj

sliced≃sigma-slice
  : T ⇑ c
  ≃ Σ[ x ꞉ C↓c.Ob {c} ] T (x .domain)
sliced≃sigma-slice = ≅ₜ→≃ sliced-iso
                   ∙ Σ-ap-snd (λ _ → ×-swap)
                   ∙ Σ-assoc
                   ∙ Σ-ap-fst (≅ₜ→≃ /-Obj-Iso) ⁻¹
