{-# OPTIONS --safe --backtracking-instance-search #-}
module Correspondences.Omniscient where

open import Meta.Prelude

open import Meta.Effect.Map

open import Correspondences.Decidable
open import Correspondences.Exhaustible

open import Data.Dec as Dec
open import Data.Empty.Base as ⊥

open import Truncation.Propositional as ∥-∥₁

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

record Omniscient {ℓᵃ : Level} (A : Type ℓᵃ) : Typeω where
  no-eta-equality
  constructor omniscient-η
  field omniscient-β : ∀{ℓ} {P : Pred A ℓ} → Decidable P → Decidable Σ[ P ]

open Omniscient public

≃→omniscient : B ≃ A → Omniscient A → Omniscient {ℓ} B
≃→omniscient e omn .omniscient-β {P} P? = ≃→dec
  (Σ-ap e λ b → subst (λ φ → P b ≃ P φ) (e.η b ⁻¹) refl)
  (omn .omniscient-β λ {x} → P? {e ⁻¹ $ x})
  where module e = Equiv e

instance
  lift-omniscient : ⦃ omn : Omniscient A ⦄ → Omniscient (Lift ℓ A)
  lift-omniscient ⦃ omn ⦄ .omniscient-β P? = Dec.dmap
    (bimap lift refl)
    (_∘ bimap lower refl)
    (omn .omniscient-β P?)

  Σ-decision
    : {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ} {B : Pred A ℓᵇ}
    → ⦃ d : Decidable B ⦄ → ⦃ omn : Omniscient A ⦄ → Decidable Σ[ B ]
  Σ-decision ⦃ omn ⦄ = omniscient-β omn auto
  {-# OVERLAPPING Σ-decision #-}



record Omniscient₁ {ℓᵃ : Level} (A : Type ℓᵃ) : Typeω where
  no-eta-equality
  constructor omniscient₁-η
  field omniscient₁-β : ∀{ℓ} {P : Pred A ℓ} → Decidable P → Decidable ∃[ P ]

open Omniscient₁ public

≃→omniscient₁ : B ≃ A → Omniscient₁ A → Omniscient₁ B
≃→omniscient₁ e omn₁ .omniscient₁-β {P} P? = ≃→dec
  (∥-∥₁.ae (Σ-ap e λ b → subst (λ φ → P b ≃ P φ) (e.η b ⁻¹) refl)) $
    omn₁ .omniscient₁-β λ {x} → P? {e ⁻¹ $ x}
  where module e = Equiv e

instance
  omniscient→omniscient₁ : ⦃ omn : Omniscient A ⦄ → Omniscient₁ A
  omniscient→omniscient₁ ⦃ omn ⦄ .omniscient₁-β d = Dec.dmap
    ∣_∣₁
    ∥-∥₁.rec!
    (omniscient-β omn d)
  {-# INCOHERENT omniscient→omniscient₁ #-}

  omniscient₁→exhaustible : ⦃ omn₁ : Omniscient₁ A ⦄ → Exhaustible A
  omniscient₁→exhaustible ⦃ omn₁ ⦄ .exhaustible-β {P} P? = Dec.dmap {P = ¬ ∃[ mapⁿ 1 ¬_ P ]}
    (λ ¬∃p x → dec→essentially-classical P? (¬∃p ∘ ∣_∣₁ ∘ (x ,_)))
    (contra λ ∀p → ∥-∥₁.rec! λ p → p .snd (∀p (p .fst)))
    (Dec-¬ ⦃ omn₁ .omniscient₁-β λ {z} → Dec-¬ ⦃ P? ⦄ ⦄)

  lift-omniscient₁ : ⦃ omn₁ : Omniscient₁ A ⦄ → Omniscient₁ (Lift ℓ A)
  lift-omniscient₁ ⦃ omn₁ ⦄ .omniscient₁-β P? = Dec.dmap
    (map (bimap lift refl))
    (contra (map (bimap lower refl)))
    (omn₁ .omniscient₁-β P?)

  Dec-∃
    : {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ} {B : Pred A ℓᵇ}
    → ⦃ d : Decidable B ⦄ → ⦃ omn₁ : Omniscient₁ A ⦄
    → Decidable ∃[ B ]
  Dec-∃ ⦃ omn₁ ⦄ = omniscient₁-β omn₁ auto
  {-# OVERLAPPABLE Dec-∃ #-}

  Dec-omni₁-prop
    : ∀{ℓᵃ ℓᵇ} {A : Type ℓᵃ} {B : Pred A ℓᵇ}
    → ⦃ ΣAB-prop : H-Level 1 Σ[ B ] ⦄
    → ⦃ d : Decidable B ⦄
    → ⦃ omn₁ : Omniscient₁ A ⦄
    → Decidable Σ[ B ]
  Dec-omni₁-prop = ∥-∥₁.proj! (∥-∥₁∘dec≃dec∘∥-∥₁ ⁻¹ $ Dec-∃)
  {-# INCOHERENT Dec-omni₁-prop #-}


-- Usage
module _
  {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ } {B : A → Type ℓᵇ} ⦃ d : Decidable B ⦄
  ⦃ A-omn₁ : Omniscient₁ A ⦄ ⦃ ΣAB-prop : H-Level 1 Σ[ B ] ⦄ where

  _ : Omniscient₁ A
  _ = autoω

  _ : Exhaustible A
  _ = autoω

  _ : Dec (Σ[ a ꞉ A ] B a)
  _ = auto

  _ : Dec (∃[ a ꞉ A ] B a)
  _ = auto
