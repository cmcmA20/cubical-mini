{-# OPTIONS --safe #-}
module Cat.Morphism.Instances where

open import Prelude
  renaming ( _↪_ to ↪ₜ
           ; _↠_ to ↠ₜ
           ; Extensional-↪ to Extensional-↪ₜ
           ; Extensional-↠ to Extensional-↠ₜ
           )

open import Cat.Base
open import Cat.Morphism
open import Cat.Morphism
  using (H-Level-inverses ; ≅-Cat-Ob) public

unquoteDecl H-Level-mono = declare-record-hlevel 2 H-Level-mono (quote _↪_)
unquoteDecl H-Level-epi = declare-record-hlevel 2 H-Level-epi (quote _↠_)

module _ {o ℓ} {C : Precategory o ℓ} where
  open Precategory C

  instance opaque
    H-Level-has-section
      : {a b : ⌞ C ⌟} {f : a ⇒ b} {n : HLevel} ⦃ _ : n ≥ʰ 2 ⦄
      → H-Level n (has-section f)
    H-Level-has-section ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $ ≅→is-of-hlevel! 2 has-section-Iso

    H-Level-has-retract
      : {a b : ⌞ C ⌟} {f : a ⇒ b} {n : HLevel} ⦃ _ : n ≥ʰ 2 ⦄
      → H-Level n (has-retract f)
    H-Level-has-retract ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $ ≅→is-of-hlevel! 2 has-retract-Iso

    H-Level-is-invertible
      : {a b : ⌞ C ⌟} {f : a ⇒ b} {n : HLevel} → ⦃ n ≥ʰ 1 ⦄
      → H-Level n (is-invertible f)
    H-Level-is-invertible ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (is-invertible-is-prop _)

    H-Level-Inverses
      : {a b : ⌞ C ⌟} {f : a ⇒ b} {g : b ⇒ a} {n : HLevel} → ⦃ n ≥ʰ 2 ⦄
      → H-Level n (Inverses f g)
    H-Level-Inverses ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $ ≅→is-of-hlevel! 2 Inverses-Iso

    H-Level-≅
      : {a b : ⌞ C ⌟} {n : HLevel} → ⦃ n ≥ʰ 2 ⦄
      → H-Level n (_≅_ ⦃ ≅-Cat-Ob C ⦄ a b)
    H-Level-≅ ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $ ≅→is-of-hlevel! 2 Iso-Iso

  instance
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
    → Extensional (_≅_ ⦃ ≅-Cat-Ob C ⦄ a b) ℓr
  Extensional-≅ ⦃ sa ⦄ = set-injective→extensional! (≅-path C) sa
