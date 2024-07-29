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

∙ₑ-id-l
  : {A : Type ℓ} {B : Type ℓ′}
    (f : A ≃ B) → refl ∙ f ＝ f
∙ₑ-id-l _ = equiv-ext refl

∙ₑ-id-r
  : {A : Type ℓ} {B : Type ℓ′}
    (f : A ≃ B) → f ∙ refl ＝ f
∙ₑ-id-r _ = equiv-ext refl

∙ₑ-assoc
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {D : Type ℓ‴}
    (f : A ≃ B) (g : B ≃ C) (h : C ≃ D)
  → f ∙ (g ∙ h) ＝ (f ∙ g) ∙ h
∙ₑ-assoc _ _ _ = equiv-ext refl

∙ₑ-inv-l
  : {A : Type ℓ} {B : Type ℓ′}
    (f : A ≃ B) → f ⁻¹ ∙ f ＝ refl
∙ₑ-inv-l f = equiv-ext $ fun-ext $ is-equiv→counit (f .snd)

∙ₑ-cancel-l
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
    (f : A ≃ B) (g : B ≃ C)
  → f ⁻¹ ∙ f ∙ g ＝ g
∙ₑ-cancel-l _ g = ∙ₑ-assoc _ _ _ ∙ ap (_∙ g) (∙ₑ-inv-l _) ∙ ∙ₑ-id-l _

∙ₑ-inv-r
  : {A : Type ℓ} {B : Type ℓ′}
    (f : A ≃ B) → f ∙ f ⁻¹ ＝ refl
∙ₑ-inv-r f = ap (_∙ f ⁻¹) (equiv-ext refl) ∙ ∙ₑ-inv-l _

∙ₑ-cancel-r
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
    (f : A ≃ B) (g : C ≃ B) → (f ∙ g ⁻¹) ∙ g ＝ f
∙ₑ-cancel-r f _ = sym (∙ₑ-assoc _ _ _) ∙ ap (f ∙_) (∙ₑ-inv-l _) ∙ ∙ₑ-id-r _

@0 ua-∙ₑ : {A B C : Type ℓ}
           (f : A ≃ B) (g : B ≃ C)
         → ua (f ∙ g) ＝ ua f ∙ ua g
ua-∙ₑ {C} = Jₑ (λ B′ f → Π[ g ꞉ B′ ≃ C ] (ua (f ∙ g) ＝ ua f ∙ ua g))
  λ g → ap ua (∙ₑ-id-l g) ∙ sym (∙-id-l (ua g)) ∙ (ap (_∙ ua g) $ sym ua-idₑ)

whisker-path-lₑ : (a ＝ c) → (a ＝ b) ≃ (c ＝ b)
whisker-path-lₑ ac = ≅→≃ $ sym ac ∙_ , iso (ac ∙_) (λ _ → ∙-cancel-l _ _) (λ _ → ∙-cancel-l _ _)

whisker-path-rₑ : (b ＝ c) → (a ＝ b) ≃ (a ＝ c)
whisker-path-rₑ bc = ≅→≃ $ _∙ bc , iso (_∙ sym bc) (λ _ → ∙-cancel-r _ _) (λ _ → ∙-cancel-r _ _)

whisker-lₑ
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
  → (A ≃ C) → (A ≃ B) ≃ (C ≃ B)
whisker-lₑ ac = ≅→≃ $ ac ⁻¹ ∙_ , iso (ac ∙_) (λ _ → ∙ₑ-cancel-l _ _) λ ab →
  ∙ₑ-assoc _ _ _ ∙ ap (_∙ ab) (∙ₑ-inv-r _) ∙ ∙ₑ-id-l _

whisker-rₑ : (B ≃ C) → (A ≃ B) ≃ (A ≃ C)
whisker-rₑ bc = ≅→≃ $ _∙ bc , iso (_∙ bc ⁻¹) (λ _ → ∙ₑ-cancel-r _ _) λ ab →
  ∙ₑ-assoc _ _ _ ⁻¹ ∙ ap (ab ∙_) (∙ₑ-inv-r _) ∙ ∙ₑ-id-r _

whisker-bothₑ : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {D : Type ℓ‴}
  → (A ≃ C) → (B ≃ D) → (A ≃ B) ≃ (C ≃ D)
whisker-bothₑ ac bd = whisker-lₑ ac ∙ whisker-rₑ bd
