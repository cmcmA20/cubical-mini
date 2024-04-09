{-# OPTIONS --safe #-}
module Data.Quotient.Set.Properties where

open import Meta.Prelude

open import Meta.Effect.Map

open import Structures.n-Type

open import Correspondences.Base
open import Correspondences.Discrete

open import Data.Dec.Base as Dec
  using (Dec)
import Data.Dec.Path
import Data.Empty.Base as ⊥
open import Data.Quotient.Set.Base
import Data.Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∃-syntax-und; ∥_∥₁ ; ∣_∣₁)

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
⦋-⦌-surjective = elim-prop! (λ a → ∣ a , refl ∣₁)

universal : is-set B
          → (A / R → B)
          ≃ Σ[ f ꞉ (A → B) ] (∀ a b → R a b → f a ＝ f b)
universal {B} {A} {R} B-set = ≅→≃ $ inc , iso back (λ _ → refl) li where
  instance _ = hlevel-basic-instance 2 B-set
  inc : (A / R → B) → Σ[ f ꞉ (A → B) ] (∀ a b → R a b → f a ＝ f b)
  inc f = f ∘ ⦋_⦌ , λ a b r i → f (glue/ a b r i)
  back = rec! $ₜ²_
  li : _
  li f′ = fun-ext λ r → ∥-∥₁.rec! (λ (_ , p) → ap (back (inc f′)) p ⁻¹ ∙ ap f′ p) (⦋-⦌-surjective r)

module @0 _ {R : Corr 2 (A , A) ℓ} (congr : is-congruence R) where
  open is-congruence congr

  Code : A → A / R → Prop ℓ
  Code x = elim! (λ y → el! $ R x y) (λ y z r →
    n-ua $ prop-extₑ! (_∙ᶜ r) (_∙ᶜ symᶜ r) )

  encode : ∀ x y (p : ⦋ x ⦌ ＝ y) → ⌞ Code x y ⌟
  encode x _ p = subst ⌞ Code x ⌟ p reflᶜ

  decode : ∀ x y (p : ⌞ Code x y ⌟) → ⦋ x ⦌ ＝ y
  decode = elim-prop! ∘ glue/

  effective : R x y
            ≃ ⦋ x ⦌ ＝ ⦋ y ⦌
  effective {x} {y} = prop-extₑ! (decode x ⦋ y ⦌) (encode x ⦋ y ⦌)

@0 equivalence→effective₁
  : Equivalence R
  → ∥ R x y ∥₁
  ≃ Path (A / λ x y → ∥ R x y ∥₁) ⦋ x ⦌ ⦋ y ⦌
equivalence→effective₁ {R} R-eq = effective ∥R∥₁-c where
  open Equivalence R-eq
  ∥R∥₁-c : is-congruence _
  ∥R∥₁-c .is-congruence.equivalenceᶜ .reflᶜ = ∣ reflᶜ ∣₁
  ∥R∥₁-c .is-congruence.equivalenceᶜ .symᶜ = map symᶜ
  ∥R∥₁-c .is-congruence.equivalenceᶜ ._∙ᶜ_ = ∥-∥₁.elim!² λ a b → ∣ a ∙ᶜ b ∣₁
  ∥R∥₁-c .is-congruence.has-propᶜ = hlevel!

/₂-is-discrete
  : (R-c : is-congruence R)
  → ⦃ d : ∀ {x y} → Dec (R x y) ⦄
  → is-discrete (A / R)
/₂-is-discrete {A} {R} R-c ⦃ d ⦄ {x} {y} = elim-prop!² {P = λ a b → Dec (a ＝ b)} go x y where
  go : (x y : A) → Dec (⦋ x ⦌ ＝ ⦋ y ⦌)
  go x y = Dec.dmap (glue/ _ _) (λ f p → ⊥.rec $ f $ effective R-c ⁻¹ $ p) d
