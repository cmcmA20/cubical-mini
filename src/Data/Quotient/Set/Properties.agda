{-# OPTIONS --safe #-}
module Data.Quotient.Set.Properties where

open import Meta.Prelude
open import Meta.Extensionality

open import Structures.n-Type

open import Data.Quotient.Set.Base
open import Data.Quotient.Set.Path
import Data.Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∥_∥₁ ; ∣_∣₁)

open import Functions.Surjection

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓᵖ ℓʳ ℓˢ ℓᵗ ℓ : Level
  A : Type ℓᵃ
  x y : A
  B : Type ℓᵇ
  C : Type ℓᶜ
  P : A → Type ℓᵖ
  R : A → A → Type ℓʳ

⦋-⦌-surjective : {A : Type ℓᵃ} {R : A → A → Type ℓʳ}
              → is-surjective (⦋_⦌ {R = R})
⦋-⦌-surjective = elim! λ a → ∣ a , refl ∣₁

universal : is-set B
          → (A / R → B)
          ≃ Σ[ f ꞉ (A → B) ] (∀ a b → R a b → f a ＝ f b)
universal {B} {A} {R} B-set = ≅→≃ $ trivial-iso! inc back where
  instance _ = hlevel-basic-instance 2 B-set
  inc : (A / R → B) → Σ[ f ꞉ (A → B) ] (∀ a b → R a b → f a ＝ f b)
  inc f = f ∘ ⦋_⦌ , λ a b r i → f (glue/ a b r i)
  back : Σ[ f ꞉ (A → B) ] (∀ a b → R a b → f a ＝ f b) → A / R → B
  back = rec hlevel! $ₜ²_

@0 equivalence→effective₁
  : Equivalence R
  → ∥ R x y ∥₁
  ≃ Path (A / λ x y → ∥ R x y ∥₁) ⦋ x ⦌ ⦋ y ⦌
equivalence→effective₁ {R} R-eq = effective ∥R∥₁-c where
  open Equivalence R-eq
  ∥R∥₁-c : is-congruence λ x y → ∥ R x y ∥₁
  ∥R∥₁-c .is-congruence.equivalence .reflexive .refl = ∣ refl ∣₁
  ∥R∥₁-c .is-congruence.equivalence .symmetric ._ᵒᵖ = map sym
  ∥R∥₁-c .is-congruence.equivalence .transitive ._∙_ = elim! λ p q → ∣ p ∙ q ∣₁
  ∥R∥₁-c .is-congruence.has-prop = hlevel 1
