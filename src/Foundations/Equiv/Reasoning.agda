{-# OPTIONS --safe #-}
module Foundations.Equiv.Reasoning where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Groupoid
open import Foundations.Equiv.Properties
open import Foundations.Path
open import Foundations.Univalence.Base

private variable ℓᵃ : Level

@0 ∙-flip-rₑ : {A : Type ℓᵃ} {a b c : A} {ab : a ＝ b} {bc : b ＝ c} {ac : a ＝ c}
             → ab ∙ bc ＝ ac
             ≃ ab      ＝ ac ∙ bc ⁻¹
∙-flip-rₑ {ab} {bc} {ac} =
  ab ∙ bc           ＝ ac          ≡⟨ ap-≃ (whisker-path-rₑ _) ⟩
  (ab ∙ bc) ∙ bc ⁻¹ ＝ ac ∙ bc ⁻¹  ≡⟨ whisker-path-lₑ (∙-cancel-r′ (∙-inv-l _)) ⟩
  ab                ＝ ac ∙ bc ⁻¹  ∎

-- it could be defined using `flip-rₑ` but the chain would be longer
@0 flip-lₑ : {A : Type ℓᵃ} {a b c : A} {ab : a ＝ b} {bc : b ＝ c} {ac : a ＝ c}
           → ab ∙ bc ＝ ac
           ≃      bc ＝ ab ⁻¹ ∙ ac
flip-lₑ {ab} {bc} {ac} =
  ab ∙ bc         ＝ ac          ≡⟨ ap-≃ (whisker-path-lₑ _) ⟩
  ab ⁻¹ ∙ ab ∙ bc ＝ ab ⁻¹ ∙ ac  ≡⟨ whisker-path-lₑ (∙-cancel-l′ (∙-inv-r _)) ⟩
  bc              ＝ ab ⁻¹ ∙ ac  ∎

@0 tiltₑ : {A : Type ℓᵃ} {a b c : A} {ab : a ＝ b} {bc : b ＝ c} {ac : a ＝ c}
         → ab ⁻¹ ∙ ac ＝ bc
         ≃ ab ＝ ac ∙ bc ⁻¹
tiltₑ = ∙-flip-rₑ ∙ ap-≃ sym-≃ ∙ whisker-path-rₑ (sym-∙ _ _)
