{-# OPTIONS --safe #-}
module Meta.Finite where

open import Foundations.Base
open import Foundations.Equiv public
open import Foundations.Sigma
open import Foundations.Pi

open import Meta.Bind
open import Meta.Discrete
open import Meta.HLevel
open import Meta.Idiom

open import Data.Empty.Base
open import Data.Nat
open import Data.Fin.Base
open import Data.Fin.Properties
open import Data.Fin.Instances.Discrete
open import Data.Fin.Closure

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

record Finite {ℓ} (T : Type ℓ) : Type ℓ where
  constructor fin
  field
    {cardinality} : ℕ
    enumeration   : ∥ T ≃ Fin cardinality ∥₁

open Finite ⦃ ... ⦄ public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : A → Type ℓ′
  B : Type ℓ′
  n : ℕ

Finite→is-set : Finite A → is-set A
Finite→is-set (fin f) =
  ∥-∥₁.rec (is-of-hlevel-is-prop 2) (λ e → is-of-hlevel-≃ 2 e hlevel!) f

Finite-choice
  : {P : A → Type ℓ′}
  → ⦃ Finite A ⦄
  → (∀ x → ∥ P x ∥₁) → ∥ (∀ x → P x) ∥₁
Finite-choice {P} ⦃ fin {(sz)} e ⦄ k = do
  e ← e
  choose ← fin-choice sz λ x → k (is-equiv→inverse (e .snd) x)
  pure $ λ x → subst P (is-equiv→unit (e .snd) x) (choose (e .fst x))

instance
  H-Level-Finite : H-Level (suc n) (Finite A)
  H-Level-Finite = prop-instance {A = Finite _} λ where
    x y i .Finite.cardinality → ∥-∥₁.proj
      ⦇ fin-injective (⦇ ⦇ x .enumeration ₑ⁻¹ ⦈ ∙ₑ y .enumeration ⦈) ⦈
      i
    x y i .Finite.enumeration → is-prop→pathP
      {B = λ i → ∥ _ ≃ Fin (∥-∥₁.proj ⦇ fin-injective (⦇ ⦇ x .enumeration ₑ⁻¹ ⦈ ∙ₑ y .enumeration ⦈) ⦈ i) ∥₁}
      (λ _ → squash₁)
      (x .enumeration) (y .enumeration) i

private
  finite-pi-fin
    : ∀ n {P : Fin n → Type ℓ′}
    → (∀ x → Finite (P x))
    → Finite ((x : Fin n) → P x)
  finite-pi-fin zero fam = fin {cardinality = 1} $ pure $ iso→equiv λ where
    .fst x → fzero
    .snd .is-iso.inv x ()
    .snd .is-iso.rinv fzero → refl
    .snd .is-iso.linv x → fun-ext λ {()}

  finite-pi-fin (suc sz) {P} fam = ∥-∥₁.proj do
    e ← fin-choice (suc sz) λ x → fam x .enumeration
    let rest = finite-pi-fin sz (λ x → fam (fsuc x))
    cont ← rest .Finite.enumeration
    let
      work = fin-suc-universal {n = sz} {A = P}
        ∙ₑ Σ-ap (e fzero) (λ x → cont)
        ∙ₑ fin-sum λ _ → rest .Finite.cardinality
    pure $ fin $ pure work

instance
  Finite-× : ⦃ Finite A ⦄ → ⦃ Finite B ⦄ → Finite (A × B)
  Finite-× {A} {B} = fin $ do
    aeq ← enumeration {T = A}
    beq ← enumeration {T = B}
    pure ((Σ-ap aeq λ _ → beq) ∙ₑ fin-product)

  Finite-Σ
    : ⦃ Finite A ⦄ → ⦃ ∀ x → Finite (P x) ⦄ → Finite (Σ A P)
  Finite-Σ {A} {P} ⦃ (afin) ⦄ ⦃ (fam) ⦄ = ∥-∥₁.proj do
    aeq ← afin .Finite.enumeration
    let
      module aeq = Equiv aeq
      bc : (x : Fin (afin .cardinality)) → ℕ
      bc x = fam (aeq.from x) .cardinality

      fs : (Σ _ λ x → Fin (bc x)) ≃ Fin (sum (afin .cardinality) bc)
      fs = fin-sum bc
      work = do
        t ← Finite-choice λ x → fam x .enumeration
        pure $ Σ-ap aeq λ x → t x
            ∙ₑ (_ , cast-is-equiv (ap (λ e → fam e .cardinality)
                      (sym (aeq.η x))))
    pure $ fin ⦇ work ∙ₑ pure fs ⦈

  Finite-Π
    : {P : A → Type ℓ′} → ⦃ Finite A ⦄ → ⦃ ∀ x → Finite (P x) ⦄ → Finite (∀ x → P x)
  Finite-Π {A} {P} ⦃ fin {(sz)} en ⦄ ⦃ (fam) ⦄ = ∥-∥₁.proj do
    eqv ← en
    let count = finite-pi-fin sz λ x → fam $ is-equiv→inverse (eqv .snd) x
    eqv′ ← count .enumeration
    pure $ fin $ pure $ Π-dom-≃ (eqv ₑ⁻¹) ∙ₑ eqv′

  Finite-Lift
    : ⦃ Finite A ⦄ → Finite (Lift ℓ′ A)
  Finite-Lift ⦃ (A-fin) ⦄ .Finite.cardinality = A-fin .cardinality
  Finite-Lift ⦃ (A-fin) ⦄ .Finite.enumeration = do
    aeq ← A-fin .enumeration
    pure $ lift-equiv ∙ₑ aeq

  -- TODO
  -- Finite-＝
  --   : ⦃ Discrete A ⦄ → ⦃ Finite A ⦄ → {x y : A} → Finite (x ＝ y)
  -- Finite-＝ {x} {y} with x ≟ y
  -- ... | yes p = fin {cardinality = 1} $ {!!}
  -- ... | no ¬p = fin {cardinality = 0} $ pure ((λ p → absurd (¬p p)) , {!!})
