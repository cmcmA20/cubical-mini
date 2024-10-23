{-# OPTIONS --safe #-}
module Data.Dec.Properties where

open import Meta.Prelude

open import Meta.Effect.Idiom

open import Data.Dec.Base as Dec
open import Data.Dec.Path
open import Data.Reflects.Base
open import Data.Empty.Base
open import Data.Empty.Properties
open import Data.Sum.Properties
import Data.Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∥_∥₁)

private variable
  ℓ ℓ′ : Level
  A P : Type ℓ
  B : Type ℓ′

∥-∥₁∘dec≃dec∘∥-∥₁ : ∥ Dec P ∥₁ ≃ Dec ∥ P ∥₁
∥-∥₁∘dec≃dec∘∥-∥₁ = prop-extₑ!
  (rec! $ Dec.dmap pure λ ¬p ∣p∣₁ → rec! ¬p ∣p∣₁)
  (Dec.rec (yes <$>_) (pure ∘ no ∘ contra pure))

ae : A ≃ B → Dec A ≃ Dec B
ae {A} {B} e = ≅→≃ $ iso to from (fun-ext ri) (fun-ext li) where
  to   = Dec.dmap (e    $_) (contra (e ⁻¹ $_))
  from = Dec.dmap (e ⁻¹ $_) (contra (e    $_))

  module e = Equiv e

  ri : from section-of′ to
  ri = Dec.elim (ap yes ∘ e.ε #_) (ap no ∘ λ _ → prop!)

  li : from retract-of′ to
  li = Dec.elim (ap yes ∘ sym ∘ e.η #_) (ap no ∘ λ _ → prop!)

≃→dec : (B ≃ A) → Dec A → Dec B
≃→dec e = ae e ⁻¹ $_

given-yes_return_then_
  : {A : Type ℓ} ⦃ d : Dec A ⦄ ⦃ A-pr : H-Level 1 A ⦄
    (a : A) (C : Dec A → Type ℓ′)
  → C (yes a) → C d
given-yes_return_then_ {A} a C cy = caseᵈ A return C of λ where
  (yes a′) → subst C prop! cy
  (no  ¬a) → false! (¬a a)

given-no_return_then_
  : {A : Type ℓ} ⦃ d : Dec A ⦄
    (¬a : ¬ A) (C : Dec A → Type ℓ′)
  → C (no ¬a) → C d
given-no_return_then_ {A} ¬a C cy = caseᵈ A return C of λ where
  (yes a)   → false! (¬a a)
  (no  ¬a′) → subst (C ∘ no) prop! cy
