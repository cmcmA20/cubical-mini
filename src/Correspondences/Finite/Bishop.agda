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
open import Meta.Variadic

open import Correspondences.Discrete
open import Correspondences.Exhaustible
open import Correspondences.Finite.ManifestBishop
open import Correspondences.Omniscient

open import Data.Dec.Path
open import Data.Empty.Base
open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Properties
open import Data.Fin.Computational.Closure
open import Data.Fin.Computational.Instances.Discrete

open import Functions.Embedding

open import Truncation.Propositional as ∥-∥₁

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : A → Type ℓ′
  B : Type ℓ′

record is-bishop-finite (A : Type ℓ) : Type ℓ where
  no-eta-equality
  constructor fin₁
  field
    { cardinality } : ℕ
    enumeration₁    : ∥ A ≃ Fin cardinality ∥₁

open is-bishop-finite public

unquoteDecl is-bishop-finite-iso = declare-record-iso is-bishop-finite-iso (quote is-bishop-finite)

instance
  H-Level-is-bishop-finite : ∀ {n} → H-Level (suc n) (is-bishop-finite A)
  H-Level-is-bishop-finite = hlevel-prop-instance $ is-of-hlevel-≃ _ (iso→equiv is-bishop-finite-iso) $ is-prop-η go where
    go : (p q : Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁) → p ＝ q
    go (m , ∣p∣₁) (n , ∣q∣₁) = Σ-prop-path! $ ∥-∥₁.elim²!
      (λ p q → fin-injective ((p ₑ⁻¹) ∙ₑ q)) ∣p∣₁ ∣q∣₁

manifest-bishop-finite→is-bishop-finite : Manifest-bishop-finite A → is-bishop-finite A
manifest-bishop-finite→is-bishop-finite fi .cardinality = fi .cardinality
manifest-bishop-finite→is-bishop-finite fi .enumeration₁ = ∣ fi .enumeration  ∣₁

is-bishop-finite→is-discrete : is-bishop-finite A → is-discrete A
is-bishop-finite→is-discrete fi = ∥-∥₁.proj! do
  e ← fi .enumeration₁
  pure $ is-discrete-embedding (equiv→embedding e) fin-is-discrete

is-bishop-finite→omniscient₁ : is-bishop-finite A → Omniscient₁ {ℓ = ℓ′} A
is-bishop-finite→omniscient₁ {A} fi .omniscient₁-β {P} P? = ∥-∥₁.proj! do
  aeq ← fi .enumeration₁
  pure $ manifest-bishop-finite→omniscient₁ (fin aeq) .omniscient₁-β P?


bishop-finite : ⦃ d : is-bishop-finite A ⦄ → is-bishop-finite A
bishop-finite ⦃ d ⦄ = d

finite-choice
  : {P : Pred A ℓ′}
  → is-bishop-finite A
  → (∀ x → ∥ P x ∥₁) → ∥ (∀ x → P x) ∥₁
finite-choice {P} A-f k = do
  e ← enumeration₁ A-f
  choose ← fin-choice (cardinality A-f) λ x → k (is-equiv→inverse (e .snd) x)
  pure $ λ x → subst P (is-equiv→unit (e .snd) x) (choose (e # x))

finite-pi-fin
  : {ℓ′ : Level} (n : ℕ) {P : Fin n → Type ℓ′}
  → (∀ x → is-bishop-finite (P x))
  → is-bishop-finite Π[ P ]
finite-pi-fin 0 {P} fam = fin₁ $ pure $ iso→equiv $ ff , iso gg ri li where
  ff : Π[ x ꞉ Fin 0 ] P x → Fin 1
  ff _ = fzero
  gg : _
  gg _ f0 = absurd (fin-0-is-initial # f0)
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


×-is-bishop-finite : is-bishop-finite A → is-bishop-finite B → is-bishop-finite (A × B)
×-is-bishop-finite afin bfin = fin₁ do
  aeq ← enumeration₁ afin
  beq ← enumeration₁ bfin
  pure $ ×-ap aeq beq ∙ₑ fin-product

Σ-is-bishop-finite
  : is-bishop-finite A → (∀ x → is-bishop-finite (P x)) → is-bishop-finite (Σ A P)
Σ-is-bishop-finite {A} {P} afin fam = ∥-∥₁.proj! do
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

fun-is-bishop-finite
  : is-bishop-finite A → is-bishop-finite B → is-bishop-finite (A → B)
fun-is-bishop-finite afin bfin = ∥-∥₁.proj! do
  ae ← enumeration₁ afin
  be ← enumeration₁ bfin
  let count = finite-pi-fin (cardinality afin) λ _ → bfin
  eqv′ ← enumeration₁ count
  pure $ fin₁ $ pure (Π-cod-≃ (λ _ → be) ∙ₑ function-≃ ae (be ₑ⁻¹) ∙ₑ eqv′)

Π-is-bishop-finite
  : {P : A → Type ℓ′} → is-bishop-finite A → (∀ x → is-bishop-finite (P x)) → is-bishop-finite (∀ x → P x)
Π-is-bishop-finite afin fam = ∥-∥₁.proj! do
  eqv ← enumeration₁ afin
  let count = finite-pi-fin (cardinality afin) λ x → fam $ is-equiv→inverse (eqv .snd) x
  eqv′ ← enumeration₁ count
  pure $ fin₁ $ pure $ Π-dom-≃ (eqv ₑ⁻¹) ∙ₑ eqv′

lift-is-bishop-finite : is-bishop-finite A → is-bishop-finite (Lift ℓ′ A)
lift-is-bishop-finite afin = fin₁ do
  aeq ← enumeration₁ afin
  pure $ lift-equiv ∙ₑ aeq

is-bishop-finite-≃ : (B ≃ A) → is-bishop-finite A → is-bishop-finite B
is-bishop-finite-≃ f afin = fin₁ do
  aeq ← enumeration₁ afin
  pure (f ∙ₑ aeq)
