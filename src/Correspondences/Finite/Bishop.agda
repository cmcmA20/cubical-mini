{-# OPTIONS --safe #-}
module Correspondences.Finite.Bishop where

open import Meta.Prelude

open import Meta.Effect.Bind
open import Meta.Record
open import Meta.Search.Discrete
open import Meta.Search.HLevel

open import Correspondences.Discrete
open import Correspondences.Exhaustible
open import Correspondences.Finite.ManifestBishop
open import Correspondences.Omniscient

open import Data.Dec.Base as Dec
open import Data.Dec.Path
open import Data.Empty.Base
open import Data.Empty.Properties
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
  H-Level-is-bishop-finite = hlevel-prop-instance $ ≃→is-of-hlevel _ (iso→≃ is-bishop-finite-iso) $ is-prop-η go where
    go : (p q : Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁) → p ＝ q
    go (m , ∣p∣₁) (n , ∣q∣₁) = Σ-prop-path! $ ∥-∥₁.elim²!
      (λ p q → fin-injective (p ⁻¹ ∙ q)) ∣p∣₁ ∣q∣₁

manifest-bishop-finite→is-bishop-finite : Manifest-bishop-finite A → is-bishop-finite A
manifest-bishop-finite→is-bishop-finite fi .cardinality = fi .cardinality
manifest-bishop-finite→is-bishop-finite fi .enumeration₁ = ∣ fi .enumeration  ∣₁

is-bishop-finite→is-discrete : is-bishop-finite A → is-discrete A
is-bishop-finite→is-discrete fi = ∥-∥₁.proj! do
  e ← fi .enumeration₁
  pure $ ↪→is-discrete (≃→↪ e) fin-is-discrete

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
  pure $ λ x → subst P (is-equiv→unit (e .snd) x) (choose (e $ x))

bishop-finite-pi-fin
  : {ℓ′ : Level} (n : ℕ) {P : Fin n → Type ℓ′}
  → (∀ x → is-bishop-finite (P x))
  → is-bishop-finite Π[ P ]
bishop-finite-pi-fin 0 {P} fam = fin₁ $ pure $ iso→≃ $ ff , iso gg ri li where
  ff : Π[ x ꞉ Fin 0 ] P x → Fin 1
  ff _ = fzero
  gg : _
  gg _ f0 = absurd (fin-0-is-initial $ f0)
  ri : gg is-right-inverse-of ff
  ri (mk-fin 0) = refl
  li : gg is-left-inverse-of ff
  li _ = fun-ext λ ()

bishop-finite-pi-fin (suc sz) {P} fam = ∥-∥₁.proj! do
  e ← fin-choice (suc sz) (enumeration₁ ∘ fam)
  let rest = bishop-finite-pi-fin sz (fam ∘ fsuc)
  cont ← enumeration₁ rest
  let
    work = fin-suc-universal {n = sz} {A = P}
         ∙ Σ-ap (e fzero) (λ x → cont)
         ∙ fin-sum {n = cardinality (fam fzero)} λ _ → cardinality rest
  pure $ fin₁ {cardinality = sum (cardinality (fam fzero)) (λ _ → cardinality rest)} $ pure work


×-is-bishop-finite : is-bishop-finite A → is-bishop-finite B → is-bishop-finite (A × B)
×-is-bishop-finite afin bfin = fin₁ do
  aeq ← enumeration₁ afin
  beq ← enumeration₁ bfin
  pure $ ×-ap aeq beq ∙ fin-product

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
           ∙ ＝→≃ (ap (λ T → Fin T) (ap (cardinality ∘ fam) (sym (aeq.η x))))

  pure $ fin₁ ⦇ work ∙ₑ pure fs ⦈

fun-is-bishop-finite
  : is-bishop-finite A → is-bishop-finite B → is-bishop-finite (A → B)
fun-is-bishop-finite afin bfin = ∥-∥₁.proj! do
  ae ← enumeration₁ afin
  be ← enumeration₁ bfin
  let count = bishop-finite-pi-fin (cardinality afin) λ _ → bfin
  eqv′ ← enumeration₁ count
  pure $ fin₁ $ pure $ Π-cod-≃ (λ _ → be) ∙ function-≃ ae (be ⁻¹) ∙ eqv′

Π-is-bishop-finite
  : {P : A → Type ℓ′} → is-bishop-finite A → (∀ x → is-bishop-finite (P x)) → is-bishop-finite (∀ x → P x)
Π-is-bishop-finite afin fam = ∥-∥₁.proj! do
  eqv ← enumeration₁ afin
  let count = bishop-finite-pi-fin (cardinality afin) (λ x → fam $ eqv ⁻¹ $ x)
  eqv′ ← enumeration₁ count
  pure $ fin₁ $ pure $ Π-dom-≃ (eqv ⁻¹) ∙ eqv′

lift-is-bishop-finite : is-bishop-finite A → is-bishop-finite (Lift ℓ′ A)
lift-is-bishop-finite afin = fin₁ do
  aeq ← enumeration₁ afin
  pure $ lift-equiv ∙ aeq

decidable-prop→is-bishop-finite : is-prop A → Dec A → is-bishop-finite A
decidable-prop→is-bishop-finite A-prop (yes a) = fin₁ $ pure $
  is-contr→equiv (inhabited-prop-is-contr a A-prop) fin-1-is-contr
decidable-prop→is-bishop-finite A-prop (no ¬a) = fin₁ $ pure $ ¬-extₑ ¬a refl ∙ fin-0-is-initial ⁻¹

is-discrete→path-is-bishop-finite : is-discrete A → {x y : A} → is-bishop-finite (x ＝ y)
is-discrete→path-is-bishop-finite d = decidable-prop→is-bishop-finite hlevel! (d .is-discrete-β _ _)
  where instance _ = d

pathP-is-bishop-finite : ∀ {A :  I → Type ℓ} → is-bishop-finite (A i1) → ∀ x y → is-bishop-finite ＜ x ／ A ＼ y ＞
pathP-is-bishop-finite f _ _ = subst is-bishop-finite (symₚ $ pathP＝path _ _ _) $
  is-discrete→path-is-bishop-finite (is-bishop-finite→is-discrete f)

≃→is-bishop-finite : (B ≃ A) → is-bishop-finite A → is-bishop-finite B
≃→is-bishop-finite f afin = fin₁ do
  aeq ← enumeration₁ afin
  pure $ f ∙ aeq

is-bishop-finite-≃ = ≃→is-bishop-finite
{-# WARNING_ON_USAGE is-bishop-finite-≃ "Use ``"  #-}
