{-# OPTIONS --safe #-}
module Foundations.Equiv.Reasoning where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Groupoid
open import Foundations.Equiv.Properties
open import Foundations.Path
open import Foundations.Univalence.Base

private variable
  ℓᵃ : Level
  A : Type ℓᵃ
  a b c : A
  ab : a ＝ b
  ac : a ＝ c
  bc : b ＝ c

@0 ∙-flip-rₑ : ab ∙ bc ＝ ac
             ≃ ab      ＝ ac ∙ sym bc
∙-flip-rₑ {ab} {bc} {ac} =
  ab ∙ bc            ＝ ac            ≃⟨ ap-≃ (whisker-path-rₑ _) ⟩
  (ab ∙ bc) ∙ sym bc ＝ ac ∙ sym bc   ≃⟨ whisker-path-lₑ (∙-cancel-r′ (∙-inv-l _)) ⟩
  ab                 ＝ ac ∙ sym bc   ≃∎

-- it could be defined using `flip-rₑ` but the chain would be longer
@0 flip-lₑ : ab ∙ bc ＝ ac
           ≃      bc ＝ sym ab ∙ ac
flip-lₑ {ab} {bc} {ac} =
  ab ∙ bc          ＝ ac            ≃⟨ ap-≃ (whisker-path-lₑ _) ⟩
  sym ab ∙ ab ∙ bc ＝ sym ab ∙ ac   ≃⟨ whisker-path-lₑ (∙-cancel-l′ (∙-inv-r _)) ⟩
  bc               ＝ sym ab ∙ ac   ≃∎

@0 tiltₑ : sym ab ∙ ac ＝ bc
         ≃     ab      ＝ ac ∙ sym bc
tiltₑ = ∙-flip-rₑ ∙ₑ ap-≃ sym-≃ ∙ₑ whisker-path-rₑ (sym-∙ _ _)
