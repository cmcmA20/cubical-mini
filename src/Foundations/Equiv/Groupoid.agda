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

instance
  Unit-l-≃ : Unit-l _≃_ (_≃_ {ℓ} {ℓ′})
  Unit-l-≃ .∙-id-l _ = equiv-ext refl

  Unit-r-≃ : Unit-r (_≃_ {ℓ} {ℓ′}) _≃_
  Unit-r-≃ .∙-id-r _ = equiv-ext refl

  Assoc-≃ : Assoc (_≃_ {ℓ} {ℓ′}) (_≃_ {_} {ℓ″}) (_≃_ {_} {ℓ‴}) _≃_ _≃_ _≃_
  Assoc-≃ .∙-assoc _ _ _ = equiv-ext refl

  Inv-l-≃ : Inv-l (_≃_ {ℓ} {ℓ′}) _≃_ _≃_
  Inv-l-≃ .∙-inv-l f = equiv-ext $ fun-ext $ is-equiv→counit (f .snd)

  Inv-r-≃ : Inv-r (_≃_ {ℓ} {ℓ′}) _≃_ _≃_
  Inv-r-≃ .∙-inv-r f = equiv-ext $ fun-ext $ is-equiv→unit (f .snd)

∙ₑ-cancel-l
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
    (f : A ≃ B) (g : B ≃ C)
  → f ⁻¹ ∙ f ∙ g ＝ g
∙ₑ-cancel-l f g = ∙-assoc (f ⁻¹) f g ∙ ap (_∙ g) (∙-inv-l f) ∙ ∙-id-l g

∙ₑ-cancel-r
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
    (f : A ≃ B) (g : C ≃ B) → (f ∙ g ⁻¹) ∙ g ＝ f
∙ₑ-cancel-r f g = ∙-assoc f _ g ⁻¹ ∙ ap (f ∙_) (∙-inv-l g) ∙ ∙-id-r f

@0 ua-∙ₑ : {A B C : Type ℓ}
           (f : A ≃ B) (g : B ≃ C)
         → ua (f ∙ g) ＝ ua f ∙ ua g
ua-∙ₑ {C} = Jₑ (λ B′ f → Π[ g ꞉ B′ ≃ C ] (ua (f ∙ g) ＝ ua f ∙ ua g))
  λ g → ap ua (∙-id-l g) ∙ sym (∙-id-l (ua g)) ∙ (ap (_∙ ua g) $ sym ua-idₑ)

whisker-path-lₑ : (a ＝ c) → (a ＝ b) ≃ (c ＝ b)
whisker-path-lₑ ac = ≅→≃ $ sym ac ∙_ , iso (ac ∙_) (λ _ → ∙-cancel-l _ _) (λ _ → ∙-cancel-l _ _)

whisker-path-rₑ : (b ＝ c) → (a ＝ b) ≃ (a ＝ c)
whisker-path-rₑ bc = ≅→≃ $ _∙ bc , iso (_∙ sym bc) (λ _ → ∙-cancel-r _ _) (λ _ → ∙-cancel-r _ _)

whisker-lₑ
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
  → (A ≃ C) → (A ≃ B) ≃ (C ≃ B)
whisker-lₑ ac = ≅→≃ $ ac ⁻¹ ∙_ , iso (ac ∙_) (λ _ → ∙ₑ-cancel-l _ _) λ ab →
  ∙-assoc ac _ _ ∙ ap (_∙ ab) # ∙-inv-r ac ∙ ∙-id-l ab

whisker-rₑ : (B ≃ C) → (A ≃ B) ≃ (A ≃ C)
whisker-rₑ bc = ≅→≃ $ _∙ bc , iso (_∙ bc ⁻¹) (λ _ → ∙ₑ-cancel-r _ _) λ ab →
  ∙-assoc ab bc _ ⁻¹ ∙ ap (ab ∙_) # ∙-inv-r bc ∙ ∙-id-r ab

whisker-bothₑ : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {D : Type ℓ‴}
  → (A ≃ C) → (B ≃ D) → (A ≃ B) ≃ (C ≃ D)
whisker-bothₑ ac bd = whisker-lₑ ac ∙ whisker-rₑ bd
