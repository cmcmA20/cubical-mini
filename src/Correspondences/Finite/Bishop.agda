{-# OPTIONS --safe #-}
module Correspondences.Finite.Bishop where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Pi
open import Foundations.Sigma
open import Foundations.Univalence

open import Meta.Bind
open import Meta.Record
open import Meta.Search.Discrete
open import Meta.Search.HLevel

open import Correspondences.Discrete
open import Correspondences.Exhaustible
open import Correspondences.Finite.ManifestBishop
open import Correspondences.Omniscient

open import Data.Dec.Path
open import Data.Empty.Base
open import Data.FinSub.Base
open import Data.FinSub.Properties
open import Data.FinSub.Closure
open import Data.FinSub.Instances.Discrete
open import Data.Nat.Instances.Discrete

open import Functions.Embedding

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : A → Type ℓ′
  B : Type ℓ′

record is-fin-set (A : Type ℓ) : Type ℓ where
  no-eta-equality
  constructor fin₁
  field
    { cardinality } : ℕ
    enumeration₁    : ∥ A ≃ Fin cardinality ∥₁

open is-fin-set public

unquoteDecl is-fin-set-iso = declare-record-iso is-fin-set-iso (quote is-fin-set)

instance
  H-Level-is-fin-set : ∀ {n} → H-Level (suc n) (is-fin-set A)
  H-Level-is-fin-set = hlevel-prop-instance $ is-of-hlevel-≃ _ (iso→equiv is-fin-set-iso) $ is-prop-η go where
    go : (p q : Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁) → p ＝ q
    go (m , ∣p∣₁) (n , ∣q∣₁) = Σ-prop-path! $ ∥-∥₁.elim²!
      (λ p q → fin-injective ((p ₑ⁻¹) ∙ₑ q)) ∣p∣₁ ∣q∣₁

𝓑→is-fin-set : 𝓑 A → is-fin-set A
𝓑→is-fin-set fi .cardinality = fi .cardinality
𝓑→is-fin-set fi .enumeration₁ = ∣ fi .enumeration  ∣₁

is-fin-set→is-discrete : is-fin-set A → is-discrete A
is-fin-set→is-discrete fi = ∥-∥₁.proj! do
  e ← fi .enumeration₁
  pure $ is-discrete-embedding (equiv→embedding e) fin-is-discrete

is-fin-set→omniscient₁ : is-fin-set A → Omniscient₁ {ℓ = ℓ′} A
is-fin-set→omniscient₁ {A} fi .omniscient₁-β {P} P? = ∥-∥₁.proj! do
  aeq ← fi .enumeration₁
  pure $ 𝓑→omniscient₁ (fin aeq) .omniscient₁-β P?


finite : ⦃ d : is-fin-set A ⦄ → is-fin-set A
finite ⦃ d ⦄ = d

finite-choice
  : {P : A → Type ℓ′}
  → is-fin-set A
  → (∀ x → ∥ P x ∥₁) → ∥ (∀ x → P x) ∥₁
finite-choice {P} A-f k = do
  e ← enumeration₁ A-f
  choose ← fin-choice (cardinality A-f) λ x → k (is-equiv→inverse (e .snd) x)
  pure $ λ x → subst P (is-equiv→unit (e .snd) x) (choose (e .fst x))

finite-pi-fin
  : (n : ℕ) {P : Fin n → Type ℓ′}
  → (∀ x → is-fin-set (P x))
  → is-fin-set Π¹[ P ]
finite-pi-fin 0 {P} fam = fin₁ $ pure $ iso→equiv $ ff , iso gg ri li where
  ff : Π[ x ꞉ Fin 0 ] P x → Fin 1
  ff _ = fzero
  gg : _
  gg _ f0 = absurd (fin-0-is-initial .fst f0)
  ri : gg is-right-inverse-of ff
  ri (mk-fin 0) = refl
  li : gg is-left-inverse-of ff
  li _ = fun-ext λ ()

finite-pi-fin (suc sz) {P} fam = ∥-∥₁.proj! do
  e ← fin-choice (suc sz) (enumeration₁ ∘ fam)
  let rest = finite-pi-fin sz (fam ∘ fsuc)
  cont ← enumeration₁ rest
  let
    work =  fin-suc-universal {n = sz} {A = P}
         ∙ₑ Σ-ap (e fzero) (λ x → cont)
         ∙ₑ fin-sum {n = cardinality (fam fzero)} λ _ → cardinality rest
  pure $ fin₁ $ pure work


×-is-fin-set : is-fin-set A → is-fin-set B → is-fin-set (A × B)
×-is-fin-set afin bfin = fin₁ do
  aeq ← enumeration₁ afin
  beq ← enumeration₁ bfin
  pure $ ×-ap aeq beq ∙ₑ fin-product

Σ-is-fin-set
  : is-fin-set A → (∀ x → is-fin-set (P x)) → is-fin-set (Σ A P)
Σ-is-fin-set {A} {P} afin fam = ∥-∥₁.proj! do
  aeq ← enumeration₁ afin
  let
    module aeq = Equiv aeq
    bc : (x : Fin (cardinality afin)) → ℕ
    bc = cardinality ∘ fam ∘ aeq.from

    fs : (Σ _ λ x → Fin (bc x)) ≃ Fin (sum (cardinality afin) bc)
    fs = fin-sum bc
    work = do
      t ← finite-choice afin $ enumeration₁ ∘ fam
      pure $ Σ-ap aeq λ x → t x
          ∙ₑ path→equiv (ap (λ T → Fin T) (ap (cardinality ∘ fam) (sym (aeq.η x))))

  pure $ fin₁ ⦇ work ∙ₑ pure fs ⦈

fun-is-fin-set
  : is-fin-set A → is-fin-set B → is-fin-set (A → B)
fun-is-fin-set afin bfin = ∥-∥₁.proj! do
  ae ← enumeration₁ afin
  be ← enumeration₁ bfin
  let count = finite-pi-fin (cardinality afin) λ _ → bfin
  eqv′ ← enumeration₁ count
  pure $ fin₁ $ pure (Π-cod-≃ (λ _ → be) ∙ₑ function-≃ ae (be ₑ⁻¹) ∙ₑ eqv′)

Π-is-fin-set
  : {P : A → Type ℓ′} → is-fin-set A → (∀ x → is-fin-set (P x)) → is-fin-set (∀ x → P x)
Π-is-fin-set afin fam = ∥-∥₁.proj! do
  eqv ← enumeration₁ afin
  let count = finite-pi-fin (cardinality afin) λ x → fam $ is-equiv→inverse (eqv .snd) x
  eqv′ ← enumeration₁ count
  pure $ fin₁ $ pure $ Π-dom-≃ (eqv ₑ⁻¹) ∙ₑ eqv′

lift-is-fin-set : is-fin-set A → is-fin-set (Lift ℓ′ A)
lift-is-fin-set afin = fin₁ do
  aeq ← enumeration₁ afin
  pure $ lift-equiv ∙ₑ aeq
