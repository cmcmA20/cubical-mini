{-# OPTIONS --safe #-}
module Cat.Morphism.Instances where

open import Prelude
  renaming ( _↪_ to ↪ₜ
           ; _↠_ to ↠ₜ
           ; Extensional-↪ to Extensional-↪ₜ
           ; Extensional-↠ to Extensional-↠ₜ
           ; _∘_ to _∘ₜ_
           )

open import Cat.Base
import Cat.Morphism

module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Morphism C

  private variable
    n : HLevel
    a b : Ob

  instance
    H-Level-inverses
      : ⦃ hl : ∀{x y} → H-Level (suc n) (Hom x y) ⦄ {f : a ⇒ b} {g : b ⇒ a}
      → H-Level n (Inverses f g)
    H-Level-inverses .H-Level.has-of-hlevel = ≅→is-of-hlevel! _ Inverses-Iso

    opaque private
      helper : ⦃ hl : ∀ {x y} → H-Level n (Hom x y) ⦄ → H-Level (suc n) (Hom a b)
      helper .H-Level.has-of-hlevel = is-of-hlevel-suc _ (hlevel _)
      {-# INCOHERENT helper #-}


  module _ ⦃ hl : ∀ {x y} → H-Level 2 (Hom x y) ⦄ where instance
    Extensional-↪
      : ∀ {ℓr} ⦃ sa : Extensional (Hom a b) ℓr ⦄
      → Extensional (a ↪ b) ℓr
    Extensional-↪ ⦃ sa ⦄ = set-injective→extensional! ↪-pathᴾ sa

    Extensional-↠
      : ∀ {ℓr} → ⦃ sa : Extensional (Hom a b) ℓr ⦄
      → Extensional (a ↠ b) ℓr
    Extensional-↠ ⦃ sa ⦄ = set-injective→extensional! ↠-pathᴾ sa

    Extensional-≅
      : ∀ {ℓr} ⦃ sa : Extensional (Hom a b) ℓr ⦄
      → Extensional (a ≅ b) ℓr
    Extensional-≅ ⦃ sa ⦄ = set-injective→extensional! ≅-path sa

    opaque
      H-Level-qinv-prop : {f : a ⇒ b} → H-Level 1 (quasi-inverse f)
      H-Level-qinv-prop {f} = hlevel-prop-instance go where
        go : is-prop (quasi-inverse f)
        go g h = p where
          module g = quasi-inverse g
          module h = quasi-inverse h
          g~h : g.inv ＝ h.inv
          g~h =
            g.inv              ~⟨ (h.inv-o ▷ g.inv) ∙ id-r _ ⟨
            g.inv ∘ f ∘ h.inv  ~⟨ sym (assoc _ _ _) ∙∙ h.inv ◁ g.inv-i ∙∙ id-l _ ⟩
            h.inv              ∎

          p : g ＝ h
          p i .quasi-inverse.inv = g~h i
          p i .quasi-inverse.inverses =
            is-prop→pathᴾ (λ i → hlevel 1 ⦃ H-Level-inverses {g = g~h i} ⦄) g.inverses h.inverses i
      {-# OVERLAPPING H-Level-qinv-prop #-}


  module _ ⦃ hl : ∀{x y} → H-Level n (Hom x y) ⦄ where instance
    H-Level-mono : H-Level n (a ↪ b)
    H-Level-mono .H-Level.has-of-hlevel = ≅→is-of-hlevel! _ ↪-Iso

    H-Level-epi : H-Level n (a ↠ b)
    H-Level-epi .H-Level.has-of-hlevel = ≅→is-of-hlevel! _ ↠-Iso

    H-Level-has-section : {f : a ⇒ b} → H-Level n (has-section f)
    H-Level-has-section .H-Level.has-of-hlevel = ≅→is-of-hlevel! _ has-section-Iso

    H-Level-has-retraction : {f : a ⇒ b} → H-Level n (has-retraction f)
    H-Level-has-retraction .H-Level.has-of-hlevel = ≅→is-of-hlevel! _ has-retraction-Iso

    H-Level-≅ : H-Level n (a ≅ b)
    H-Level-≅ .H-Level.has-of-hlevel = ≅→is-of-hlevel! _ Iso-Iso

    opaque
      H-Level-qinv-default : {f : a ⇒ b} ⦃ _ : n ≥ʰ 2 ⦄ → H-Level n (quasi-inverse f)
      H-Level-qinv-default .H-Level.has-of-hlevel = ≅→is-of-hlevel! _ quasi-inverse-Iso
      {-# INCOHERENT H-Level-qinv-default #-}
