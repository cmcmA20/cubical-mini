{-# OPTIONS --safe --backtracking-instance-search #-}
module Categories.Morphism.Instances where

open import Prelude
  renaming ( _↪_ to ↪ₜ
           ; _↠_ to ↠ₜ
           ; _≅_ to _≅ₜ_
           ; Extensional-↪ to Extensional-↪ₜ
           ; Extensional-↠ to Extensional-↠ₜ
           )

open import Categories.Base
open import Categories.Morphism

unquoteDecl H-Level-mono = declare-record-hlevel 2 H-Level-mono (quote _↪_)
unquoteDecl H-Level-epi = declare-record-hlevel 2 H-Level-epi (quote _↠_)
unquoteDecl H-Level-section = declare-record-hlevel 2 H-Level-section (quote has-section)
unquoteDecl H-Level-retract = declare-record-hlevel 2 H-Level-retract (quote has-retract)
unquoteDecl H-Level-inverses = declare-record-hlevel 1 H-Level-inverses (quote Inverses)

instance opaque
  H-Level-is-invertible
    : ∀ {o ℓ} {C : Precategory o ℓ} {a b} {f : C .Hom a b} {n}
    → H-Level (suc n) (is-invertible C f)
  H-Level-is-invertible = hlevel-prop-instance (is-invertible-is-prop _)

unquoteDecl H-Level-≅ = declare-record-hlevel 2 H-Level-≅ (quote _≅_)

module _ {o ℓ} {C : Precategory o ℓ} where instance
  Extensional-↪
    : ∀ {ℓr} {a b}
    → ⦃ sa : Extensional (C .Hom a b) ℓr ⦄
    → Extensional (_↪_ C a b) ℓr
  Extensional-↪ ⦃ sa ⦄ = set-injective→extensional! (↪-pathᴾ C) sa

  Extensional-↠
    : ∀ {ℓr} {a b}
    → ⦃ sa : Extensional (C .Hom a b) ℓr ⦄
    → Extensional (_↠_ C a b) ℓr
  Extensional-↠ ⦃ sa ⦄ = set-injective→extensional! (↠-pathᴾ C) sa

  Extensional-≅
    : ∀ {ℓr} {a b}
    → ⦃ sa : Extensional (C .Hom a b) ℓr ⦄
    → Extensional (_≅_ C a b) ℓr
  Extensional-≅ ⦃ sa ⦄ = set-injective→extensional! (≅-path C) sa
