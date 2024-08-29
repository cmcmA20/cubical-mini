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
open import Order.SupLattice.SmallBasis

import Order.Reasoning

module _ {o ℓ ℓ′} {A B : 𝒰 ℓ′}
         {P : Poset o ℓ}
         {L : is-sup-lattice P ℓ′}
         {β : B → ⌞ P ⌟}
         (f : A ↠ B)
         where

  ↓ᴮ-surj : {x : ⌞ P ⌟}
         → ↓ᴮ {B = A} P L (β ∘ₜ f #_) x ↠ ↓ᴮ P L β x
  ↓ᴮ-surj {x} =
      (λ where (a , le) → f # a , le)
    , λ where (b , le) → rec! (λ a e → ∣ (a , subst (λ q → P .Poset._≤_ (β q) x) (e ⁻¹) le) , Σ-prop-path! e ∣₁) (f .snd b)

  cover-preserves-basis : is-basis P L β → is-basis {B = A} P L (β ∘ₜ f #_)
  cover-preserves-basis H .is-basis.≤-is-small x a = H .is-basis.≤-is-small x (f # a)
  cover-preserves-basis H .is-basis.↓-is-sup x =
    cover-preserves-is-lub ↓ᴮ-surj (H .is-basis.↓-is-sup x)

{-
  -- TODO this requires is-of-size-is-prop
  @0 cover-reflects-basis : is-basis {B = A} P L (β ∘ₜ f #_) → is-basis P L β
  cover-reflects-basis H .is-basis.≤-is-small x b =
    rec! ? (f .snd b)
  cover-reflects-basis H .is-basis.↓-is-sup x =
    cover-reflects-is-lub ↓ᴮ-surj (H .is-basis.↓-is-sup x)
-}

module _ {o₁ o₂ ℓ₁ ℓ₂ ℓ′} {B : 𝒰 ℓ′}
         {P₁ : Poset o₁ ℓ₁} {P₂ : Poset o₂ ℓ₂}
         {L₁ : is-sup-lattice P₁ ℓ′} {L₂ : is-sup-lattice P₂ ℓ′}
         {β₁ : B → ⌞ P₁ ⌟}
  where

  -- TODO use proper order equivalences

  ≃→is-basis : (e : ⌞ P₁ ⌟ ≃ ⌞ P₂ ⌟)
             → (∀ {x y} → Poset._≤_ P₁ x y → Poset._≤_ P₂ (e $ x) (e $ y))
             → (∀ {x y} → Poset._≤_ P₂ (e $ x) (e $ y) → Poset._≤_ P₁ x y)
             → is-basis P₁ L₁ β₁
             → is-basis P₂ L₂ (e #_ ∘ₜ β₁)
  ≃→is-basis e f g H₁ .is-basis.≤-is-small x b =
    let (v , eq) = H₁ .is-basis.≤-is-small (e ⁻¹ $ x) b in
    v , (eq ∙ prop-extₑ! (f {x = β₁ b} {y = e ⁻¹ $ x}) g ∙ =→≃ (ap (P₂ Poset.≤ (e $ β₁ b)) (is-equiv→counit (e .snd) x)))
  ≃→is-basis e f g H₁ .is-basis.↓-is-sup x =
     cast-is-lub (Σ-ap-snd λ b → prop-extₑ! (f {x = β₁ b} {y = e ⁻¹ $ x}) g ∙ =→≃ (ap (P₂ Poset.≤ (e $ β₁ b)) (is-equiv→counit (e .snd) x)))
                 (λ i → refl) $
     subst (is-lub P₂ (λ i → e $ β₁ (i .fst))) (is-equiv→counit (e .snd) x) $
     ≃→is-lub {P = P₁} {Q = P₂} e f g $
     H₁ .is-basis.↓-is-sup (e ⁻¹ $ x)

module _ {o₁ o₂ ℓ₁ ℓ₂ ℓ′} {B : 𝒰 ℓ′}
         {P₁ : Poset o₁ ℓ₁} {P₂ : Poset o₂ ℓ₂}
         {L₁ : is-sup-lattice P₁ ℓ′} {L₂ : is-sup-lattice P₂ ℓ′}
         {β₂ : B → ⌞ P₂ ⌟}
  where

  ≃→is-basis′ : (e : ⌞ P₁ ⌟ ≃ ⌞ P₂ ⌟)
             → (∀ {x y} → Poset._≤_ P₁ x y → Poset._≤_ P₂ (e $ x) (e $ y))
             → (∀ {x y} → Poset._≤_ P₂ (e $ x) (e $ y) → Poset._≤_ P₁ x y)
             → is-basis P₁ L₁ ((e ⁻¹) #_ ∘ₜ β₂)
             → is-basis P₂ L₂ β₂
  ≃→is-basis′ e f g H₁ =
    subst (is-basis P₂ L₂) (fun-ext λ b → is-equiv→counit (e .snd) (β₂ b)) $
    ≃→is-basis {P₂ = P₂} {L₂ = L₂} e f g H₁

module _ {o₁ ℓ₁ o₂ ℓ₂ ℓ} {B₁ B₂ : 𝒰 ℓ}
         {P₁ : Poset o₁ ℓ₁} {P₂ : Poset o₂ ℓ₂}
         {L₁ : is-sup-lattice P₁ ℓ} {L₂ : is-sup-lattice P₂ ℓ}
         {β₁ : B₁ → ⌞ P₁ ⌟} {β₂ : B₂ → ⌞ P₂ ⌟}
         where

  -- to build a product basis we need to construct surjections between ↓ᴮ (x,y) and ↓ᴮ x / ↓ᴮ y
  -- one way to do this is to require β₁/β₂ to have fibers at ⊥
  ×-⊥-small-basis : ∥ fibre β₁ (is-sup-lattice.bot L₁) ∥₁
                   → ∥ fibre β₂ (is-sup-lattice.bot L₂) ∥₁
                   → is-basis P₁ L₁ β₁
                   → is-basis P₂ L₂ β₂
                   → is-basis {B = B₁ × B₂} (P₁ × P₂) (L₁ × L₂)
                              < β₁ ∘ₜ fst , β₂ ∘ₜ snd >
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

module _ {o ℓ ℓ′} {B : 𝒰 ℓ′}
         {P : Poset o ℓ}
         {L : is-sup-lattice P ℓ′}
         {β : B → ⌞ P ⌟}
         where

  -- to guarantee that β has a fiber at ⊥, we can freely add it via Maybe
  maybe-basis : is-basis P L β → is-basis {B = Maybe B} P L (recᵐ (is-sup-lattice.bot L) β)
  maybe-basis H .is-basis.≤-is-small x (just b) = H .is-basis.≤-is-small x b
  maybe-basis H .is-basis.≤-is-small x nothing = ⊤ , lift≃id ∙ is-contr→equiv-⊤
                                                     (inhabited-prop-is-contr (is-sup-lattice.has-bot L x) (P .Poset.≤-thin)) ⁻¹
  maybe-basis H .is-basis.↓-is-sup x .is-lub.fam≤lub (mb , le) = le
  maybe-basis H .is-basis.↓-is-sup x .is-lub.least ub f =
    H .is-basis.↓-is-sup x .is-lub.least ub λ where (b , le) → f (just b , le)
