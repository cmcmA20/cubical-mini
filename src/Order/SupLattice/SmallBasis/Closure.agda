{-# OPTIONS --safe #-}
module Order.SupLattice.SmallBasis.Closure where

open import Categories.Prelude

open import Functions.Surjection

open import Data.Unit
open import Data.Maybe renaming (rec to recᵐ)

open import Order.Diagram.Lub
open import Order.Base
open import Order.Category
open import Order.SupLattice
open import Order.Constructions.Product

import Order.Reasoning

open import Order.SupLattice.SmallBasis

module _ {o₁ ℓ₁ o₂ ℓ₂ ℓ} {B₁ B₂ : 𝒰 ℓ}
         (P₁ : Poset o₁ ℓ₁) (P₂ : Poset o₂ ℓ₂)
         (L₁ : is-sup-lattice P₁ ℓ) (L₂ : is-sup-lattice P₂ ℓ)
         (β₁ : B₁ → ⌞ P₁ ⌟) (β₂ : B₂ → ⌞ P₂ ⌟)
         (H₁ : is-basis P₁ L₁ β₁) (H₂ : is-basis P₂ L₂ β₂)
         where

  -- to build a product basis we need to construct surjections between ↓ᴮ (x,y) and ↓ᴮ x / ↓ᴮ y
  -- one way to do this is to require β₁/β₂ to have fibers at ⊥
  ×-⊥-small-basis : ∥ fibre β₁ (is-sup-lattice.bot L₁) ∥₁
                   → ∥ fibre β₂ (is-sup-lattice.bot L₂) ∥₁
                   → is-basis {B = B₁ × B₂} (P₁ × P₂) (L₁ × L₂)
                              < β₁ ∘ₜ fst , β₂ ∘ₜ snd >
  ×-⊥-small-basis fb₁ fb₂ .is-basis.≤-is-small (x₁ , x₂) (b₁ , b₂) =
    ×-is-of-size (H₁ .is-basis.≤-is-small x₁ b₁) (H₂ .is-basis.≤-is-small x₂ b₂)
  ×-⊥-small-basis fb₁ fb₂ .is-basis.↓-is-sup (x₁ , x₂) =
    ×-is-lub-surj
       ( (λ where
              ((b₁ , b₂) , le₁ , le₂) → b₁ , le₁)
       , λ where
             (b₁ , le₁) → map (λ where
                                   (b₀ , e₀) →
                                       ((b₁ , b₀) , (le₁ , subst (λ q → P₂ .Poset._≤_ q x₂) (e₀ ⁻¹) (is-sup-lattice.has-bot L₂ x₂)))
                                     , refl)
                              fb₂)
       ( (λ where
              ((b₁ , b₂) , le₁ , le₂) → b₂ , le₂)
       , λ where
             (b₂ , le₂) → map (λ where
                                   (b₀ , e₀) →
                                       ((b₀ , b₂) , (subst (λ q → P₁ .Poset._≤_ q x₁) (e₀ ⁻¹) (is-sup-lattice.has-bot L₁ x₁) , le₂))
                                     , refl)
                              fb₁)
       (H₁ .is-basis.↓-is-sup x₁)
       (H₂ .is-basis.↓-is-sup x₂)

module _ {o ℓ ℓ′} {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (H : is-basis P L β)
         where

  -- to guarantee that β has a fiber at ⊥, we can freely add it via Maybe
  maybe-basis : is-basis {B = Maybe B} P L (recᵐ (is-sup-lattice.bot L) β)
  maybe-basis .is-basis.≤-is-small x (just b) = H .is-basis.≤-is-small x b
  maybe-basis .is-basis.≤-is-small x nothing = ⊤ , lift≃id ∙ is-contr→equiv-⊤
                                                     (inhabited-prop-is-contr (is-sup-lattice.has-bot L x) (P .Poset.≤-thin)) ⁻¹
  maybe-basis .is-basis.↓-is-sup x .is-lub.fam≤lub (mb , le) = le
  maybe-basis .is-basis.↓-is-sup x .is-lub.least ub f =
    H .is-basis.↓-is-sup x .is-lub.least ub λ where (b , le) → f (just b , le)
