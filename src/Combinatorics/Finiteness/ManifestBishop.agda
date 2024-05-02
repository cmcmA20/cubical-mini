{-# OPTIONS --safe #-}
module Combinatorics.Finiteness.ManifestBishop where

open import Meta.Prelude

open import Meta.Deriving.HLevel
open import Meta.Ord
open import Meta.Record

open import Logic.Discreteness
open import Logic.Omniscience

open import Data.Empty.Base
open import Data.Dec.Base as Dec
open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Closure
open import Data.Fin.Computational.Instances.Discrete
open import Data.Fin.Computational.Instances.Ord
open import Data.Nat
open import Data.Vec.Inductive.Base
open import Data.Vec.Inductive.Operations.Computational
open import Data.Vec.Inductive.Correspondences.Unary.Any.Computational
open import Data.Truncation.Propositional as ∥-∥₁

open import Functions.Embedding


private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  P : A → Type ℓ

record Manifest-bishop-finite (A : Type ℓ) : Type ℓ where
  no-eta-equality
  constructor fin
  field
    { cardinality } : ℕ
    enumeration     : A ≃ Fin cardinality

open Manifest-bishop-finite public

unquoteDecl manifest-bishop-finite-iso =
  declare-record-iso manifest-bishop-finite-iso (quote Manifest-bishop-finite)

unquoteDecl H-Level-manifest-bishop-finite =
  declare-record-hlevel 2 H-Level-manifest-bishop-finite (quote Manifest-bishop-finite)

instance
  lift-manifest-bishop-finite
    : ⦃ mbf : Manifest-bishop-finite A ⦄
    → Manifest-bishop-finite (Lift ℓ A)
  lift-manifest-bishop-finite ⦃ mbf ⦄ = fin $ lift≃id ∙ enumeration mbf

  manifest-bishop-finite→ord
    : ⦃ mbf : Manifest-bishop-finite A ⦄
    → Ord A
  manifest-bishop-finite→ord = ≃→ord (auto .enumeration) Ord-Fin

  ×-manifest-bishop-finite
    : ⦃ A-mbf : Manifest-bishop-finite A ⦄ ⦃ B-mbf : Manifest-bishop-finite B ⦄
    → Manifest-bishop-finite (A × B)
  ×-manifest-bishop-finite = fin $ ×-ap (enumeration auto) (enumeration auto) ∙ fin-product
  {-# OVERLAPPING ×-manifest-bishop-finite #-}

private
  finite-pi-fin
    : {ℓ′ : Level} (n : ℕ) {P : Fin n → Type ℓ′}
    → (∀ x → Manifest-bishop-finite (P x))
    → Manifest-bishop-finite Π[ P ]
  finite-pi-fin 0 {P} fam = fin $ ≅→≃ $ ff , iso gg ri li where
    ff : Π[ x ꞉ Fin 0 ] P x → Fin 1
    ff _ = fzero
    gg : Fin 1 → Π[ x ꞉ Fin 0 ] P x
    gg _ f₀ = absurd $ fin-0-is-initial $ f₀
    ri : gg is-right-inverse-of ff
    ri (mk-fin 0) = refl
    li : gg is-left-inverse-of ff
    li _ = fun-ext λ ()

  finite-pi-fin (suc sz) {P} fam =
    let e    = enumeration ∘ fam
        rest = finite-pi-fin sz (fam ∘ fsuc)
        cont = enumeration rest
    in fin {cardinality = sum (fam fzero .cardinality) (λ _ → rest .cardinality)}
         $ fin-suc-universal ∙ ×-ap (e fzero) cont ∙ fin-sum λ _ → cardinality rest

instance
  Σ-manifest-bishop-finite
    : ∀{ℓ ℓᵃ} {A : Type ℓᵃ} {P : A → Type ℓ}
      ⦃ A-mbf : Manifest-bishop-finite A ⦄
    → ⦃ fam : ∀ {x : A} → Manifest-bishop-finite (P x) ⦄
    → Manifest-bishop-finite Σ[ P ]
  Σ-manifest-bishop-finite {A} {P} ⦃ A-mbf ⦄ ⦃ fam ⦄ =
    let aeq = enumeration auto
        module aeq = Equiv aeq
        fs = fin-sum $ cardinality ∘ (λ z → fam {z}) ∘ aeq.from
        work = Σ-ap aeq λ x
          → enumeration (fam {x})
          ∙ ＝→≃ (ap (λ T → Fin T) (ap (cardinality ∘ (λ z → fam {z})) (sym (aeq.η x))))
    in fin $ work ∙ fs
  {-# OVERLAPPABLE Σ-manifest-bishop-finite #-}

  fun-manifest-bishop-finite
    : ⦃ A-mbf : Manifest-bishop-finite A ⦄
    → ⦃ B-mbf : Manifest-bishop-finite B ⦄
    → Manifest-bishop-finite (A → B)
  fun-manifest-bishop-finite ⦃ A-mbf ⦄ ⦃ B-mbf ⦄ =
    let ae = enumeration A-mbf
        be = enumeration B-mbf
        count = finite-pi-fin (cardinality A-mbf) λ _ → B-mbf
    in fin $ Π-cod-≃ (λ _ → be) ∙ function-≃ ae (be ⁻¹) ∙ enumeration count
  {-# OVERLAPPING fun-manifest-bishop-finite #-}

  Π-manifest-bishop-finite
    : {ℓ ℓ′ : Level} {A : Type ℓ} {P : A → Type ℓ′}
    → ⦃ A-mbf : Manifest-bishop-finite A ⦄
    → ⦃ fam : ∀ {x} → Manifest-bishop-finite (P x) ⦄
    → Manifest-bishop-finite Π[ P ]
  Π-manifest-bishop-finite ⦃ A-mbf ⦄ ⦃ fam ⦄ =
    let e = enumeration A-mbf
        module e = Equiv e
        count = finite-pi-fin (cardinality A-mbf) ((λ z → fam {z}) ∘ e.from)
    in fin $ Π-dom-≃ e.inverse ∙ enumeration count

  manifest-bishop-finite→omniscient
    : ⦃ mbf : Manifest-bishop-finite A ⦄
    → Omniscient A
  manifest-bishop-finite→omniscient {A} ⦃ mbf ⦄ .omniscient-β {P} P? =
    Dec.dmap lemma₁ lemma₂ (any? (λ {x} → P? {x}) {xs})
    where
      n = mbf .cardinality
      module Ã = Equiv (mbf .enumeration)
      module Ṽ = Equiv vec-fun-equiv

      xs : Vec A n
      xs = Ṽ.from $ Ã.from

      lemma₁ : Σ[ i ꞉ Fin n ] P (lookup xs i) → Σ[ a ꞉ A ] P a
      lemma₁ = bimap (lookup xs) refl

      lemma₂ : ¬ Σ[ i ꞉ Fin n ] P (lookup xs i) → ¬ Σ[ a ꞉ A ] P a
      lemma₂ = contra $ bimap Ã.to λ {a} →
        subst P $ (happly (Ṽ.ε Ã.from) (Ã.to a) ∙ Ã.η a) ⁻¹


≃→manifest-bishop-finite : (B ≃ A) → Manifest-bishop-finite A → Manifest-bishop-finite B
≃→manifest-bishop-finite f afin = fin $ f ∙ enumeration afin
