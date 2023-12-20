{-# OPTIONS --safe #-}
open import Categories.Prelude

module Categories.Constructions.Sliced {o h} (C : Precategory o h) where

open import Categories.Constructions.Slice C
import Categories.Morphism

open Precategory C
module C↓c {c} = Categories.Morphism (Slice c)

private variable c : Ob

record _⇑_ {ℓ} (T : Pred Ob ℓ) (c : Ob) : 𝒰 (ℓ ⊔ o ⊔ h) where
  constructor _↑_
  field
    {support} : Ob
    thing     : T support
    thinning  : Hom support c

unquoteDecl sliced-iso = declare-record-iso sliced-iso (quote _⇑_)

private variable
  ℓ : Level
  T : Pred Ob ℓ

open /-Obj

sliced≃sigma-slice
  : T ⇑ c
  ≃ Σ[ x ꞉ C↓c.Ob {c} ] T (x .domain)
sliced≃sigma-slice =  isoₜ→equiv sliced-iso
                   ∙ₑ Σ-ap-snd (λ _ → ×-swap)
                   ∙ₑ Σ-assoc
                   ∙ₑ Σ-ap-fst (isoₜ→equiv /-Obj-iso) ₑ⁻¹
