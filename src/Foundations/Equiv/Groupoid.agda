{-# OPTIONS --safe #-}
module Foundations.Equiv.Groupoid where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.Isomorphism
open import Foundations.Path
open import Foundations.Univalence.Base

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : Type ℓ
  a b c : A
  B : Type ℓ′
  C : Type ℓ″
  D : Type ℓ‴

∙ₑ-id-l : (f : A ≃ B) → idₑ ∙ₑ f ＝ f
∙ₑ-id-l _ = equiv-ext refl

∙ₑ-id-r : (f : A ≃ B) → f ∙ₑ idₑ ＝ f
∙ₑ-id-r _ = equiv-ext refl

∙ₑ-assoc : (f : A ≃ B) (g : B ≃ C) (h : C ≃ D)
         → f ∙ₑ (g ∙ₑ h) ＝ (f ∙ₑ g) ∙ₑ h
∙ₑ-assoc _ _ _ = equiv-ext refl

∙ₑ-inv-l : (f : A ≃ B) → f ₑ⁻¹ ∙ₑ f ＝ idₑ
∙ₑ-inv-l f = equiv-ext $ fun-ext $ is-equiv→counit (f .snd)

∙ₑ-cancel-l : (f : A ≃ B) (g : B ≃ C)
            → f ₑ⁻¹ ∙ₑ f ∙ₑ g ＝ g
∙ₑ-cancel-l _ g = ∙ₑ-assoc _ _ _ ∙ ap (_∙ₑ g) (∙ₑ-inv-l _) ∙ ∙ₑ-id-l _

∙ₑ-inv-r : (f : A ≃ B) → f ∙ₑ f ₑ⁻¹ ＝ idₑ
∙ₑ-inv-r f = ap (_∙ₑ f ₑ⁻¹) (equiv-ext refl) ∙ ∙ₑ-inv-l _

∙ₑ-cancel-r : (f : A ≃ B) (g : C ≃ B)
            → (f ∙ₑ g ₑ⁻¹) ∙ₑ g ＝ f
∙ₑ-cancel-r f _ = sym (∙ₑ-assoc _ _ _) ∙ ap (f ∙ₑ_) (∙ₑ-inv-l _) ∙ ∙ₑ-id-r _

@0 ua-∙ₑ : {A B C : Type ℓ}
           (f : A ≃ B) (g : B ≃ C)
         → ua (f ∙ₑ g) ＝ ua f ∙ ua g
ua-∙ₑ {C} = Jₑ (λ B′ f → Π[ g ꞉ B′ ≃ C ] (ua (f ∙ₑ g) ＝ ua f ∙ ua g))
  λ g → ap ua (∙ₑ-id-l g) ∙ sym (∙-id-l (ua g)) ∙ (ap (_∙ ua g) $ sym ua-idₑ)

whisker-path-lₑ : (a ＝ c) → (a ＝ b) ≃ (c ＝ b)
whisker-path-lₑ ac = iso→equiv $ sym ac ∙_ , iso (ac ∙_) (λ _ → ∙-cancel-l _ _) (λ _ → ∙-cancel-l _ _)

whisker-path-rₑ : (b ＝ c) → (a ＝ b) ≃ (a ＝ c)
whisker-path-rₑ bc = iso→equiv $ _∙ bc , iso (_∙ sym bc) (λ _ → ∙-cancel-r _ _) (λ _ → ∙-cancel-r _ _)

whisker-lₑ : (A ≃ C) → (A ≃ B) ≃ (C ≃ B)
whisker-lₑ ac = iso→equiv $ ac ₑ⁻¹ ∙ₑ_ , iso (ac ∙ₑ_) (λ _ → ∙ₑ-cancel-l _ _) λ ab →
  ∙ₑ-assoc _ _ _ ∙ ap (_∙ₑ ab) (∙ₑ-inv-r _) ∙ ∙ₑ-id-l _

whisker-rₑ : (B ≃ C) → (A ≃ B) ≃ (A ≃ C)
whisker-rₑ bc = iso→equiv $ _∙ₑ bc , iso (_∙ₑ bc ₑ⁻¹) (λ _ → ∙ₑ-cancel-r _ _) λ ab →
  sym (∙ₑ-assoc _ _ _) ∙ ap (ab ∙ₑ_) (∙ₑ-inv-r _) ∙ ∙ₑ-id-r _
