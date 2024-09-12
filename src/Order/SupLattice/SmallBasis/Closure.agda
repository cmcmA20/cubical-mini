{-# OPTIONS --safe #-}
module Order.SupLattice.SmallBasis.Closure where

open import Cat.Prelude
open import Functions.Surjection

open import Data.Unit
open import Data.Maybe renaming (rec to recᵐ)

open import Order.Diagram.Lub
open import Order.Base
open import Order.Category
open import Order.SupLattice
open import Order.Constructions.Product
open import Order.SupLattice.SmallBasis

import Order.Reasoning

module _ {o ℓ ℓ′}
         {P : Poset o ℓ} {L : is-sup-lattice P ℓ′}
         {A B : 𝒰 ℓ′} {β : B → ⌞ P ⌟}
         (f : A ↠ B)
         where

  ↓ᴮ-surj : {x : ⌞ P ⌟}
         → ↓ᴮ L (β ∘ₜ f #_) x ↠ ↓ᴮ L β x
  ↓ᴮ-surj {x} =
      (λ where (a , le) → f # a , le)
    , λ where (b , le) → rec! (λ a e → ∣ (a , subst (λ q → P .Poset._≤_ (β q) x) (e ⁻¹) le) , Σ-prop-path! e ∣₁) (f .snd b)

  cover-preserves-basis : is-basis L β → is-basis L (β ∘ₜ f #_)
  cover-preserves-basis H .is-basis.≤-is-small x a = H .is-basis.≤-is-small x (f # a)
  cover-preserves-basis H .is-basis.↓-is-sup x =
    cover-preserves-is-lub ↓ᴮ-surj (H .is-basis.↓-is-sup x)

{-
  -- TODO this requires is-of-size-is-prop
  @0 cover-reflects-basis : is-basis L (β ∘ₜ f #_) → is-basis L β
  cover-reflects-basis H .is-basis.≤-is-small x b =
    rec! ? (f .snd b)
  cover-reflects-basis H .is-basis.↓-is-sup x =
    cover-reflects-is-lub ↓ᴮ-surj (H .is-basis.↓-is-sup x)
-}

module _ {o₁ o₂ ℓ₁ ℓ₂ ℓ′}
         {P₁ : Poset o₁ ℓ₁} {P₂ : Poset o₂ ℓ₂}
         {L₁ : is-sup-lattice P₁ ℓ′} {L₂ : is-sup-lattice P₂ ℓ′}
         {B : 𝒰 ℓ′} {β₁ : B → ⌞ P₁ ⌟}
  where
  private
    module P₁ = Poset P₁
    module P₂ = Poset P₂
  open Iso

  ≅→is-basis : (e : P₁ ≅ P₂)
             → is-basis L₁ β₁ → is-basis L₂ (β₁ ∙ e #_)
  ≅→is-basis e H₁ .is-basis.≤-is-small x b = H₁ .is-basis.≤-is-small (e .from # x) b & second
    (_∙ prop-extₑ!
          (e .to #_)
          (λ z → =→~⁻ (e .inv-i #ₚ β₁ b) ∙ e .from # z ∙ =→~ (ap (e .from #_) (e .inv-o #ₚ x)))
      ∙ =→≃ (ap (e # β₁ b P₂.≤_) (e .inv-o #ₚ x)))
  ≅→is-basis e H₁ .is-basis.↓-is-sup x = cast-is-lub
    (Σ-ap-snd λ b
      → prop-extₑ!
          (e .to #_)
          (λ z → =→~⁻ (e .inv-i #ₚ β₁ b) ∙ e .from # z ∙ =→~ (ap (e .from #_) (e .inv-o #ₚ x)))
      ∙ =→≃ (ap (e # β₁ b P₂.≤_) (e .inv-o #ₚ x)))
    (λ _ → refl) $
      subst (is-lub P₂ _) (e .inv-o #ₚ x) $ ≅→is-lub e $ H₁ .is-basis.↓-is-sup (e .from # x)

module _ {o₁ o₂ ℓ₁ ℓ₂ ℓ′}
         {P₁ : Poset o₁ ℓ₁} {L₁ : is-sup-lattice P₁ ℓ′}
         {P₂ : Poset o₂ ℓ₂} {L₂ : is-sup-lattice P₂ ℓ′}
         {B : 𝒰 ℓ′} {β₂ : B → ⌞ P₂ ⌟}
  where
  open Iso

  ≅→is-basis⁻ : (e : P₁ ≅ P₂)
              → is-basis L₁ (β₂ ∙ e .from #_) → is-basis L₂ β₂
  ≅→is-basis⁻ e H₁ = subst (is-basis L₂)
    -- incredible bullshit
    (fun-ext λ b → e .to .hom # (e .inv-i #ₚ _ ⁻¹) ∙ e .to .hom # (e .from .hom # (e .inv-o #ₚ β₂ b)) ∙ e .inv-o #ₚ β₂ b)
    (≅→is-basis e H₁)

module _ {o₁ ℓ₁ o₂ ℓ₂ ℓ}
         {P₁ : Poset o₁ ℓ₁} {L₁ : is-sup-lattice P₁ ℓ}
         {P₂ : Poset o₂ ℓ₂} {L₂ : is-sup-lattice P₂ ℓ}
         {B₁ B₂ : 𝒰 ℓ} {β₁ : B₁ → ⌞ P₁ ⌟} {β₂ : B₂ → ⌞ P₂ ⌟}
         where

  -- to build a product basis we need to construct surjections between ↓ᴮ (x,y) and ↓ᴮ x / ↓ᴮ y
  -- one way to do this is to require β₁/β₂ to have fibers at ⊥
  ×-⊥-small-basis : ∥ fibre β₁ (is-sup-lattice.bot L₁) ∥₁
                   → ∥ fibre β₂ (is-sup-lattice.bot L₂) ∥₁
                   → is-basis L₁ β₁
                   → is-basis L₂ β₂
                   → is-basis (L₁ × L₂) < β₁ ∘ₜ fst , β₂ ∘ₜ snd >
  ×-⊥-small-basis fb₁ fb₂ H₁ H₂ .is-basis.≤-is-small (x₁ , x₂) (b₁ , b₂) =
    ×-is-of-size (H₁ .is-basis.≤-is-small x₁ b₁) (H₂ .is-basis.≤-is-small x₂ b₂)
  ×-⊥-small-basis fb₁ fb₂ H₁ H₂ .is-basis.↓-is-sup (x₁ , x₂) =
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

module _ {o ℓ ℓ′}
         {P : Poset o ℓ} {L : is-sup-lattice P ℓ′}
         {B : 𝒰 ℓ′} {β : B → ⌞ P ⌟}
         where

  -- to guarantee that β has a fiber at ⊥, we can freely add it via Maybe
  maybe-basis : is-basis L β → is-basis L (recᵐ (is-sup-lattice.bot L) β)
  maybe-basis H .is-basis.≤-is-small x (just b) = H .is-basis.≤-is-small x b
  maybe-basis H .is-basis.≤-is-small x nothing = ⊤ , lift≃id ∙ is-contr→equiv-⊤
                                                     (inhabited-prop-is-contr (is-sup-lattice.has-bot L x) (P .Poset.≤-thin)) ⁻¹
  maybe-basis H .is-basis.↓-is-sup x .is-lub.fam≤lub (mb , le) = le
  maybe-basis H .is-basis.↓-is-sup x .is-lub.least ub f =
    H .is-basis.↓-is-sup x .is-lub.least ub λ where (b , le) → f (just b , le)
