{-# OPTIONS --safe #-}
module Correspondences.Finite.Bishop where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Pi
open import Foundations.Sigma

open import Meta.Bind
open import Meta.Search.Discrete
open import Meta.Search.HLevel

open import Correspondences.Discrete
open import Correspondences.Exhaustible
open import Correspondences.Finite.ManifestBishop
open import Correspondences.Omniscient

open import Data.Dec.Base as Dec
open import Data.Dec.Instances.HLevel
open import Data.Empty.Base
open import Data.Fin.Base
open import Data.Fin.Properties
open import Data.Fin.Closure
open import Data.Fin.Instances.Discrete
open import Data.Nat.Instances.Discrete

open import Functions.Embedding

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : A → Type ℓ′
  B : Type ℓ′

opaque
  is-fin-set : Type ℓ → Type ℓ
  is-fin-set A = Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁

opaque
  unfolding is-fin-set
  is-fin-set-β : is-fin-set A → Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁
  is-fin-set-β = id

  is-fin-set-η : Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁ → is-fin-set A
  is-fin-set-η = id

  fin : {n : ℕ} → ∥ A ≃ Fin n ∥₁ → is-fin-set A
  fin = _ ,_

  cardinality : is-fin-set A → ℕ
  cardinality = fst

  enumeration : (A-f : is-fin-set A) → ∥ A ≃ Fin (cardinality A-f) ∥₁
  enumeration = snd

  is-fin-set-is-prop : is-prop (is-fin-set A)
  is-fin-set-is-prop = is-prop-η go where
    go : _
    go (m , ∣p∣₁) (n , ∣q∣₁) = Σ-prop-path! $ ∥-∥₁.elim₂!
      (λ p q → fin-injective ((p ₑ⁻¹) ∙ₑ q)) ∣p∣₁ ∣q∣₁

  opaque
    unfolding 𝓑

    𝓑→is-fin-set : 𝓑 A → is-fin-set A
    𝓑→is-fin-set (n , e) = n , ∣ e ∣₁

    is-fin-set→is-discrete : is-fin-set A → is-discrete A
    is-fin-set→is-discrete (_ , e) = ∥-∥₁.proj! do
      e ← e
      pure $ is-discrete-embedding (equiv→embedding e) fin-is-discrete

    opaque
      unfolding is-omniscient
      is-fin-set→is-omniscient : is-fin-set A → is-omniscient {ℓ′ = ℓ′} A
      is-fin-set→is-omniscient {A} (n , ∣aeq∣₁) {P} P? = ∥-∥₁.proj! do
        aeq ← ∣aeq∣₁
        pure $ 𝓑→is-omniscient (n , aeq) P?


finite : ⦃ d : is-fin-set A ⦄ → is-fin-set A
finite ⦃ d ⦄ = d

opaque
  unfolding is-fin-set
  finite-choice
    : {P : A → Type ℓ′}
    → is-fin-set A
    → (∀ x → ∥ P x ∥₁) → ∥ (∀ x → P x) ∥₁
  finite-choice {P} (sz , e) k = do
    e ← e
    choose ← fin-choice sz λ x → k (is-equiv→inverse (e .snd) x)
    pure $ λ x → subst P (is-equiv→unit (e .snd) x) (choose (e .fst x))


is-fin-set-is-of-hlevel : (n : HLevel) → is-of-hlevel (suc n) (is-fin-set A)
is-fin-set-is-of-hlevel _ = is-prop→is-of-hlevel-suc is-fin-set-is-prop

private
  finite-pi-fin
    : (n : ℕ) {P : Fin n → Type ℓ′}
    → (∀ x → is-fin-set (P x))
    → is-fin-set ((x : Fin n) → P x)
  finite-pi-fin zero fam = is-fin-set-η $ 1 , (pure $ iso→equiv go) where
    go : Iso _ _
    go .fst _ = fzero
    go .snd .is-iso.inv _ ()
    go .snd .is-iso.rinv fzero = refl
    go .snd .is-iso.linv _ = fun-ext λ()

  finite-pi-fin (suc sz) {P} fam = ∥-∥₁.proj (is-fin-set-is-of-hlevel _) do
    e ← fin-choice (suc sz) (enumeration ∘ fam)
    let rest = finite-pi-fin sz (fam ∘ fsuc)
    cont ← enumeration rest
    let
      work =  fin-suc-universal {n = sz} {A = P}
           ∙ₑ Σ-ap (e fzero) (λ x → cont)
           ∙ₑ fin-sum λ _ → cardinality rest
    pure $ is-fin-set-η $ _ , pure work


×-is-fin-set : is-fin-set A → is-fin-set B → is-fin-set (A × B)
×-is-fin-set afin bfin = fin do
  aeq ← enumeration afin
  beq ← enumeration bfin
  pure $ Σ-ap aeq (λ _ → beq) ∙ₑ fin-product

Σ-is-fin-set
  : is-fin-set A → (∀ x → is-fin-set (P x)) → is-fin-set (Σ A P)
Σ-is-fin-set {A} {P} afin fam = ∥-∥₁.proj (is-fin-set-is-of-hlevel _) do
  aeq ← enumeration afin
  let
    module aeq = Equiv aeq
    bc : (x : Fin (cardinality afin)) → ℕ
    bc = cardinality ∘ fam ∘ aeq.from

    fs : (Σ _ λ x → Fin (bc x)) ≃ Fin (sum (cardinality afin) bc)
    fs = fin-sum bc
    work = do
      t ← finite-choice afin $ enumeration ∘ fam
      pure $ Σ-ap aeq λ x → t x
          ∙ₑ (_ , cast-is-equiv (ap (cardinality ∘ fam)
                    (sym $ aeq.η x)))
  pure $ fin ⦇ work ∙ₑ pure fs ⦈

Π-is-fin-set
  : {P : A → Type ℓ′} → is-fin-set A → (∀ x → is-fin-set (P x)) → is-fin-set (∀ x → P x)
Π-is-fin-set afin fam = ∥-∥₁.proj (is-fin-set-is-of-hlevel _) do
  eqv ← enumeration afin
  let count = finite-pi-fin (cardinality afin) λ x → fam $ is-equiv→inverse (eqv .snd) x
  eqv′ ← enumeration count
  pure $ fin $ pure $ Π-dom-≃ (eqv ₑ⁻¹) ∙ₑ eqv′

lift-is-fin-set : is-fin-set A → is-fin-set (Lift ℓ′ A)
lift-is-fin-set afin = fin do
  aeq ← enumeration afin
  pure $ lift-equiv ∙ₑ aeq
