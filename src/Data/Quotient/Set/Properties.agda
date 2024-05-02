{-# OPTIONS --safe #-}
module Data.Quotient.Set.Properties where

open import Meta.Prelude

open import Meta.Effect.Map
open import Meta.Extensionality

open import Correspondences.Binary.Equivalence
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
⦋-⦌-surjective = elim! λ a → ∣ a , refl ∣₁

universal : is-set B
          → (A / R → B)
          ≃ Σ[ f ꞉ (A → B) ] (∀ a b → R a b → f a ＝ f b)
universal {B} {A} {R} B-set = ≅→≃ $ inc , iso back (λ _ → refl) li where
  instance _ = hlevel-basic-instance 2 B-set
  inc : (A / R → B) → Σ[ f ꞉ (A → B) ] (∀ a b → R a b → f a ＝ f b)
  inc f = f ∘ ⦋_⦌ , λ a b r i → f (glue/ a b r i)
  back : Σ[ f ꞉ (A → B) ] (∀ a b → R a b → f a ＝ f b) → A / R → B
  back = rec hlevel! $ₜ²_
  li : _
  li f′ = ext λ r → case ⦋-⦌-surjective r of λ _ p →
    ap (back (inc f′)) p ⁻¹ ∙ ap f′ p

module @0 _ {R : Corr 2 (A , A) ℓ} (congr : is-congruence R) where
  open is-congruence congr

  Code : A → A / R → Prop ℓ
  Code x = elim hlevel! (λ y → el! $ R x y) λ y z r →
    ext (prop-extₑ! (_∙ r) (_∙ r ⁻¹))

  encode : ∀ x y (p : ⦋ x ⦌ ＝ y) → ⌞ Code x y ⌟
  encode x _ p = subst ⌞ Code x ⌟ p refl

  decode : ∀ x y (p : ⌞ Code x y ⌟) → ⦋ x ⦌ ＝ y
  decode = elim! ∘ glue/

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
  ∥R∥₁-c .is-congruence.equivalence .reflexive .refl = ∣ refl ∣₁
  ∥R∥₁-c .is-congruence.equivalence .symmetric ._⁻¹ = map sym
  ∥R∥₁-c .is-congruence.equivalence .transitive ._∙_ = elim! λ a b → ∣ a ∙ b ∣₁
  ∥R∥₁-c .is-congruence.has-prop = hlevel!

/₂-is-discrete
  : (R-c : is-congruence R)
  → ⦃ d : ∀ {x y} → Dec (R x y) ⦄
  → is-discrete (A / R)
/₂-is-discrete {A} {R} R-c ⦃ d ⦄ {x = x/} {y = y/} =
  elim! {P = λ x → (y : A / R) → Dec (x ＝ y)}
    (λ x y → Dec.dmap (glue/ x y) (λ f p → ⊥.rec $ f $ effective R-c ⁻¹ $ p) d)
    x/ y/
