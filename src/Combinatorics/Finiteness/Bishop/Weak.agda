{-# OPTIONS --safe #-}
module Combinatorics.Finiteness.Bishop.Weak where

open import Meta.Prelude
open import Meta.Deriving.HLevel
open import Meta.Effect.Bind
open import Meta.Extensionality
open import Meta.Record

open import Logic.Discreteness
open import Logic.Omniscience

open import Combinatorics.Finiteness.Bishop.Manifest

open import Data.Dec.Base as Dec
open import Data.Dec.Path
open import Data.Empty.Base
open import Data.Empty.Properties
open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Properties
open import Data.Fin.Computational.Closure
open import Data.Fin.Computational.Instances.Discrete
open import Data.Nat.Path
open import Data.Truncation.Propositional as ∥-∥₁

open import Functions.Embedding

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : A → Type ℓ′
  B : Type ℓ′

record is-bishop-finite (A : Type ℓ) : Type ℓ where
  no-eta-equality
  constructor finite₁
  field
    { cardinality } : ℕ
    enumeration₁    : ∥ A ≃ Fin cardinality ∥₁

open is-bishop-finite public

unquoteDecl is-bishop-finite-iso = declare-record-iso is-bishop-finite-iso (quote is-bishop-finite)

unique-cardinality : is-prop (Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁)
unique-cardinality (m , ∣p∣₁) (n , ∣q∣₁) = ext (
  case ∣p∣₁ of λ p → case ∣q∣₁ of λ q → fin-injective (p ⁻¹ ∙ q) )

private instance
  H-Level-card : ∀{n} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁)
  H-Level-card ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance unique-cardinality

instance
  H-Level-is-bishop-finite : ∀ {n} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (is-bishop-finite A)
  H-Level-is-bishop-finite ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance $ ≅→is-of-hlevel! 1 is-bishop-finite-iso
  {-# OVERLAPPING H-Level-is-bishop-finite #-}

  manifest-bishop-finite→is-bishop-finite
    : ⦃ mbf : Manifest-bishop-finite A ⦄
    → is-bishop-finite A
  manifest-bishop-finite→is-bishop-finite ⦃ mbf ⦄ .cardinality = mbf .cardinality
  manifest-bishop-finite→is-bishop-finite ⦃ mbf ⦄ .enumeration₁ = pure $ mbf .enumeration
  {-# INCOHERENT manifest-bishop-finite→is-bishop-finite #-}

≃→is-bishop-finite : (B ≃ A) → is-bishop-finite A → is-bishop-finite B
≃→is-bishop-finite f afin = finite₁ do
  aeq ← enumeration₁ afin
  pure $ f ∙ aeq

-- ae : A ≃ B → is-bishop-finite A ≃ is-bishop-finite B
-- ae e = prop-extₑ! (≃→is-bishop-finite (e ⁻¹)) (≃→is-bishop-finite e)

∥-∥₁∘manifest-bishop-finite≃is-bishop-finite : ∥ Manifest-bishop-finite A ∥₁ ≃ is-bishop-finite A
∥-∥₁∘manifest-bishop-finite≃is-bishop-finite {A} =
  ∥ Manifest-bishop-finite A ∥₁
    ~⟨ ∥-∥₁.ae (≅→≃ manifest-bishop-finite-iso) ⟩
  ∥ Σ[ n ꞉ ℕ ] (A ≃ Fin n) ∥₁
    ~⟨ prop-extₑ! (rec! ⦃ ∥-∥₁.Inductive-∥-∥₁ ⦃ Inductive-Σ ⦃ Inductive-default ⦄ ⦄ ⦄ λ n e →
                    n , pure e)
                  (λ (n , ∣e∣₁) → map (n ,_) ∣e∣₁)
     ⟩
  Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁
    ~⟨ ≅→≃ is-bishop-finite-iso ⟨
  is-bishop-finite A
    ∎


instance
  is-bishop-finite→is-discrete
    : ⦃ bf : is-bishop-finite A ⦄
    → is-discrete A
  is-bishop-finite→is-discrete {A} ⦃ bf ⦄ = ∥-∥₁.proj! go where
    go : ∥ is-discrete A ∥₁
    go = do
      e ← bf .enumeration₁
      pure $ λ {x} {y} → ≃→is-discrete e fin-is-discrete
  {-# OVERLAPS is-bishop-finite→is-discrete #-}

  is-bishop-finite→omniscient₁ : ⦃ bf : is-bishop-finite A ⦄ → Omniscient₁ A
  is-bishop-finite→omniscient₁ {A} ⦃ bf ⦄ .omniscient₁-β {P} P? = ∥-∥₁.proj! do
    aeq ← bf .enumeration₁
    let omn = manifest-bishop-finite→omniscient ⦃ finite aeq ⦄
    pure $ omniscient→omniscient₁ ⦃ omn ⦄ .omniscient₁-β P?
  {-# OVERLAPPING is-bishop-finite→omniscient₁ #-}

finite-choice
  : {P : Pred A ℓ′}
  → is-bishop-finite A
  → (∀ x → ∥ P x ∥₁) → ∥ (∀ x → P x) ∥₁
finite-choice {P} fi k = do
  e ← enumeration₁ fi
  let module e = Equiv e
  choose ← fin-choice (cardinality fi) (k ∘ e.from)
  pure $ λ x → substₚ P (e.η x) (choose (e $ x))

private
  bishop-finite-pi-fin
    : {ℓ′ : Level} (n : ℕ) {P : Fin n → Type ℓ′}
    → (∀ x → is-bishop-finite (P x))
    → is-bishop-finite Π[ P ]
  bishop-finite-pi-fin 0 {P} fam = finite₁ $ pure $ ≅→≃ $ ff , iso gg ri li where
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
    pure $ finite₁ {cardinality = sum (cardinality (fam fzero)) (λ _ → cardinality rest)} $ pure work

instance
  ×-is-bishop-finite
    : ⦃ A-bf : is-bishop-finite A ⦄ ⦃ B-bf : is-bishop-finite B ⦄
    → is-bishop-finite (A × B)
  ×-is-bishop-finite ⦃ A-bf ⦄ ⦃ B-bf ⦄ = finite₁ do
    aeq ← enumeration₁ A-bf
    beq ← enumeration₁ B-bf
    pure $ ×-ap aeq beq ∙ fin-product
  {-# OVERLAPPING ×-is-bishop-finite #-}

  Σ-is-bishop-finite
    : ⦃ A-bf : is-bishop-finite A ⦄ → ⦃ fam : ∀ {x} → is-bishop-finite (P x) ⦄
    → is-bishop-finite (Σ A P)
  Σ-is-bishop-finite {A} {P} ⦃ A-bf ⦄ ⦃ fam ⦄ = ∥-∥₁.proj! do
    aeq ← enumeration₁ A-bf
    let
      module aeq = Equiv aeq
      bc : (x : Fin (cardinality A-bf)) → ℕ
      bc = cardinality ∘ (λ z → fam {z}) ∘ aeq.from

      fs : (Σ _ λ x → Fin (bc x)) ≃ Fin (sum (cardinality A-bf) bc)
      fs = fin-sum bc
      work = do
        t ← finite-choice A-bf $ enumeration₁ ∘ (λ z → fam {z})
        pure $ Σ-ap aeq λ x → t x
             ∙ =→≃ (ap (λ T → Fin T) (ap (cardinality ∘ (λ z → fam {z})) (sym (aeq.η x))))

    pure $ finite₁ ⦇ work ∙ₑ pure fs ⦈
  {-# OVERLAPS Σ-is-bishop-finite #-}

  fun-is-bishop-finite
    : ⦃ A-bf : is-bishop-finite A ⦄ → ⦃ B-bf : is-bishop-finite B ⦄
    → is-bishop-finite (A → B)
  fun-is-bishop-finite ⦃ A-bf ⦄ ⦃ B-bf ⦄ = ∥-∥₁.proj! do
    ae ← enumeration₁ A-bf
    be ← enumeration₁ B-bf
    let count = bishop-finite-pi-fin (cardinality A-bf) λ _ → B-bf
    eqv′ ← enumeration₁ count
    pure $ finite₁ $ pure $ Π-cod-≃ (λ _ → be) ∙ function-≃ ae (be ⁻¹) ∙ eqv′
  {-# OVERLAPPING fun-is-bishop-finite #-}

  Π-is-bishop-finite
    : {ℓ ℓ′ : Level} {A : Type ℓ} {P : A → Type ℓ′}
    → ⦃ A-bf : is-bishop-finite A ⦄ → ⦃ fam : ∀ {x} → is-bishop-finite (P x) ⦄
    → is-bishop-finite Π[ P ]
  Π-is-bishop-finite ⦃ A-bf ⦄ ⦃ fam ⦄ = ∥-∥₁.proj! do
    eqv ← enumeration₁ A-bf
    let count = bishop-finite-pi-fin (cardinality A-bf) (λ x → fam {eqv ⁻¹ $ x})
    eqv′ ← enumeration₁ count
    pure $ finite₁ $ pure $ Π-dom-≃ (eqv ⁻¹) ∙ eqv′
  {-# OVERLAPS Π-is-bishop-finite #-}

  lift-is-bishop-finite : ⦃ A-bf : is-bishop-finite A ⦄ → is-bishop-finite (Lift ℓ′ A)
  lift-is-bishop-finite ⦃ A-bf ⦄ = finite₁ do
    aeq ← enumeration₁ A-bf
    pure $ lift≃id ∙ aeq
  {-# OVERLAPPING lift-is-bishop-finite #-}

  decidable-prop→is-bishop-finite : ⦃ A-pr : H-Level 1 A ⦄ → ⦃ da : Dec A ⦄ → is-bishop-finite A
  decidable-prop→is-bishop-finite ⦃ A-pr ⦄ ⦃ yes a ⦄ = finite₁ $ pure $
    is-contr→≃ (inhabited-prop-is-contr a (hlevel 1)) fin-1-is-contr
  decidable-prop→is-bishop-finite ⦃ A-pr ⦄ ⦃ no ¬a ⦄ = finite₁ $ pure $ ¬-extₑ ¬a refl ∙ fin-0-is-initial ⁻¹
  {-# INCOHERENT decidable-prop→is-bishop-finite #-}

  is-discrete→path-is-bishop-finite : ⦃ d : is-discrete A ⦄ → {x y : A} → is-bishop-finite (x ＝ y)
  is-discrete→path-is-bishop-finite ⦃ d ⦄ = decidable-prop→is-bishop-finite ⦃ auto ⦄ ⦃ d ⦄
  {-# OVERLAPPING is-discrete→path-is-bishop-finite #-}

  -- TODO check if it's useful
  pathᴾ-is-bishop-finite
    : ∀ {A :  I → Type ℓ}
    → ⦃ bf : is-bishop-finite (A i1) ⦄ → ∀ {x y}
    → is-bishop-finite ＜ x ／ A ＼ y ＞
  pathᴾ-is-bishop-finite = substₚ is-bishop-finite (pathᴾ=path _ _ _ ⁻¹)
    is-discrete→path-is-bishop-finite
