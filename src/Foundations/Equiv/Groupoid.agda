{-# OPTIONS --safe #-}
module Foundations.Equiv.Groupoid where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.Isomorphism
open import Foundations.Path
open import Foundations.Univalence

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : Type ℓ
  a b c : A
  B : Type ℓ′
  C : Type ℓ″
  D : Type ℓ‴

instance
  GUnit-o-≃ : GUnit-o _≃_ (_≃_ {ℓ} {ℓ′})
  GUnit-o-≃ .∙-id-o _ = equiv-ext refl

  GUnit-i-≃ : GUnit-i (_≃_ {ℓ} {ℓ′}) _≃_
  GUnit-i-≃ .∙-id-i _ = equiv-ext refl

  GAssoc-≃ : GAssoc (_≃_ {ℓ} {ℓ′}) (_≃_ {_} {ℓ″}) (_≃_ {_} {ℓ‴}) _≃_ _≃_ _≃_
  GAssoc-≃ .∙-assoc _ _ _ = equiv-ext refl

  GInv-o-≃ : GInv-o (_≃_ {ℓ} {ℓ′}) _≃_ _≃_
  GInv-o-≃ .∙-inv-o f = equiv-ext $ fun-ext $ is-equiv→counit (f .snd)

  GInv-i-≃ : GInv-i (_≃_ {ℓ} {ℓ′}) _≃_ _≃_
  GInv-i-≃ .∙-inv-i f = equiv-ext $ fun-ext $ is-equiv→unit (f .snd)

∙ₑ-cancel-l
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
    (f : A ≃ B) (g : B ≃ C)
  → f ⁻¹ ∙ f ∙ g ＝ g
∙ₑ-cancel-l f g = ∙-assoc (f ⁻¹) f g ∙ (∙-inv-o f ▷ g) ∙ ∙-id-o g

∙ₑ-cancel-r
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
    (f : A ≃ B) (g : C ≃ B) → (f ∙ g ⁻¹) ∙ g ＝ f
∙ₑ-cancel-r f g = ∙-assoc f _ g ⁻¹ ∙ (f ◁ ∙-inv-o g) ∙ ∙-id-i f

@0 ua-∙ₑ : {A B C : Type ℓ}
           (f : A ≃ B) (g : B ≃ C)
         → ua (f ∙ g) ＝ ua f ∙ ua g
ua-∙ₑ {C} = Jₑ (λ B′ f → Π[ g ꞉ B′ ≃ C ] (ua (f ∙ g) ＝ ua f ∙ ua g))
  λ g → ap ua (∙-id-o g) ∙ ((ua-idₑ ▷ ua g) ∙ ∙-id-o (ua g)) ⁻¹

whisker-path-lₑ : (a ＝ c) → (a ＝ b) ≃ (c ＝ b)
whisker-path-lₑ ac = ≅→≃ $ iso (ac ⁻¹ ∙_) (ac ∙_)
  (fun-ext $ ∙-cancel-l $ ac   )
  (fun-ext $ ∙-cancel-l $ ac ⁻¹)

whisker-path-rₑ : (b ＝ c) → (a ＝ b) ≃ (a ＝ c)
whisker-path-rₑ bc = ≅→≃ $ iso (_∙ bc) (_∙ bc ⁻¹)
  (fun-ext λ ac → ∙-cancel-r ac $ bc   )
  (fun-ext λ ab → ∙-cancel-r ab $ bc ⁻¹)

whisker-lₑ
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
  → (A ≃ C) → (A ≃ B) ≃ (C ≃ B)
whisker-lₑ ac = ≅→≃ $ iso (ac ⁻¹ ∙_) (ac ∙_)
  (fun-ext $ ∙ₑ-cancel-l ac)
  (fun-ext λ ab → ∙-assoc ac _ ab ∙ (∙-inv-i ac ▷ ab) ∙ ∙-id-o ab)

whisker-rₑ : (B ≃ C) → (A ≃ B) ≃ (A ≃ C)
whisker-rₑ bc = ≅→≃ $ iso (_∙ bc) (_∙ bc ⁻¹)
  (fun-ext λ ac → ∙ₑ-cancel-r ac bc)
  (fun-ext λ ab → ∙-assoc ab bc _ ⁻¹ ∙ (ab ◁ ∙-inv-i bc) ∙ ∙-id-i ab)

whisker-bothₑ : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {D : Type ℓ‴}
  → (A ≃ C) → (B ≃ D) → (A ≃ B) ≃ (C ≃ D)
whisker-bothₑ ac bd = whisker-lₑ ac ∙ whisker-rₑ bd
