{-# OPTIONS --safe #-}
module Correspondences.Finite.ManifestBishop where

open import Meta.Prelude

open import Meta.Record
open import Meta.Search.Discrete
open import Meta.Search.HLevel

open import Correspondences.Omniscient

open import Data.Empty.Base
open import Data.Dec.Base as Dec
open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Closure
open import Data.Fin.Computational.Instances.Discrete
open import Data.Nat
open import Data.Vec.Inductive.Base
open import Data.Vec.Inductive.Operations.Computational
open import Data.Vec.Inductive.Correspondences.Unary.Any.Computational

open import Functions.Embedding

open import Truncation.Propositional as ∥-∥₁

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

unquoteDecl manifest-bishop-finite-iso = declare-record-iso manifest-bishop-finite-iso (quote Manifest-bishop-finite)

instance
  H-Level-is-manifest-bishop-finite : ∀ {n} → H-Level (2 + n) (Manifest-bishop-finite A)
  H-Level-is-manifest-bishop-finite = hlevel-basic-instance 2 $ ≃→is-of-hlevel 2 (≅→≃ manifest-bishop-finite-iso)
    (Σ-is-of-hlevel _ (ℕ-is-of-hlevel _) (λ _ → hlevel!))

manifest-bishop-finite : ⦃ d : Manifest-bishop-finite A ⦄ → Manifest-bishop-finite A
manifest-bishop-finite ⦃ d ⦄ = d

manifest-bishop-finite→omniscient₁ : Manifest-bishop-finite A → Omniscient₁ {ℓ} A
manifest-bishop-finite→omniscient₁ {A} fi .omniscient₁-β {P} P? =
  Dec.dmap lemma₁ lemma₂ (any? P? xs) where
    n = fi .cardinality
    aeq = fi .enumeration
    module Ã = Equiv aeq
    module Ṽ = Equiv vec-fun-equiv

    xs : Vec A n
    xs = Ṽ.from $ Ã.from

    lemma₁ : Σ[ i ꞉ Fin n ] P (lookup xs i) → ∥ Σ[ a ꞉ A ] P a ∥₁
    lemma₁ = ∣_∣₁ ∘′ bimap (lookup xs) refl

    lemma₂ : ¬ Σ[ i ꞉ Fin n ] P (lookup xs i) → ¬ ∥ Σ[ a ꞉ A ] P a ∥₁
    lemma₂ ¬p = ∥-∥₁.rec! $ ¬p ∘′ bimap Ã.to (subst P (sym (happly (Ṽ.ε _) _ ∙ Ã.η _)))

lift-manifest-bishop-finite : Manifest-bishop-finite A → Manifest-bishop-finite (Lift ℓ A)
lift-manifest-bishop-finite afin = fin $ lift≃id ∙ enumeration afin

×-manifest-bishop-finite : Manifest-bishop-finite A → Manifest-bishop-finite B → Manifest-bishop-finite (A × B)
×-manifest-bishop-finite afin bfin = fin $ ×-ap (enumeration afin) (enumeration bfin) ∙ fin-product

manifest-bishop-finite→is-discrete : Manifest-bishop-finite A → is-discrete A
manifest-bishop-finite→is-discrete fi = ↪→is-discrete (≃→↪ (fi .enumeration)) fin-is-discrete

finite-pi-fin
  : {ℓ′ : Level} (n : ℕ) {P : Fin n → Type ℓ′}
  → (∀ x → Manifest-bishop-finite (P x))
  → Manifest-bishop-finite Π[ P ]
finite-pi-fin 0 {P} fam = fin $ ≅→≃ $ ff , iso gg ri li where
  ff : Π[ x ꞉ Fin 0 ] P x → Fin 1
  ff _ = fzero
  gg : _
  gg _ f0 = absurd $ fin-0-is-initial $ f0
  ri : gg is-right-inverse-of ff
  ri (mk-fin 0) = refl
  li : gg is-left-inverse-of ff
  li _ = fun-ext λ ()

finite-pi-fin (suc sz) {P} fam =
  let e = enumeration ∘ fam
      rest = finite-pi-fin sz (fam ∘ fsuc)
      cont = enumeration rest
  in fin {cardinality = sum (fam fzero .cardinality) (λ _ → rest .cardinality)}
       $ fin-suc-universal ∙ ×-ap (e fzero) cont ∙ fin-sum λ _ → cardinality rest

Σ-manifest-bishop-finite
  : Manifest-bishop-finite A → (∀ x → Manifest-bishop-finite (P x)) → Manifest-bishop-finite (Σ A P)
Σ-manifest-bishop-finite {A} {P} afin fam =
  let aeq = enumeration afin
      module aeq = Equiv aeq
      fs = fin-sum $ cardinality ∘ fam ∘ aeq.from
      work = Σ-ap aeq λ x → enumeration (fam x) ∙ ＝→≃ (ap (λ T → Fin T) (ap (cardinality ∘ fam) (sym (aeq.η x))))
  in fin $ work ∙ fs

fun-manifest-bishop-finite
  : Manifest-bishop-finite A → Manifest-bishop-finite B → Manifest-bishop-finite (A → B)
fun-manifest-bishop-finite afin bfin =
  let ae = enumeration afin
      be = enumeration bfin
      count = finite-pi-fin (cardinality afin) λ _ → bfin
  in fin $ Π-cod-≃ (λ _ → be) ∙ function-≃ ae (be ⁻¹) ∙ enumeration count

Π-manifest-bishop-finite
  : {P : A → Type ℓ} → Manifest-bishop-finite A → (∀ x → Manifest-bishop-finite (P x)) → Manifest-bishop-finite (∀ x → P x)
Π-manifest-bishop-finite afin fam =
  let e = enumeration afin
      module e = Equiv e
      count = finite-pi-fin (cardinality afin) (fam ∘ e.from)
  in fin $ Π-dom-≃ e.inverse ∙ enumeration count

≃→manifest-bishop-finite : (B ≃ A) → Manifest-bishop-finite A → Manifest-bishop-finite B
≃→manifest-bishop-finite f afin = fin $ f ∙ enumeration afin

manifest-bishop-finite-≃ = ≃→manifest-bishop-finite
{-# WARNING_ON_USAGE manifest-bishop-finite-≃ "Use `≃→manifest-bishop-finite`" #-}
