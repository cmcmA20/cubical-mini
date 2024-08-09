{-# OPTIONS --safe #-}
module Data.Quotient.Set.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Structures.n-Type

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Dec.Path
open import Data.Empty.Base as ⊥
open import Data.Quotient.Set.Base as /₂
open import Data.Reflects.Base as Reflects

private variable
  ℓ ℓᵃ : Level
  A : Type ℓᵃ
  R : A → A → Type ℓ
  a b x y : A

instance opaque
  H-Level-/₂
    : ∀{ℓᵃ ℓ}{A : Type ℓᵃ} {R : A → A → 𝒰 ℓ}
    → ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n (A / R)
  H-Level-/₂ ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 squash/
  {-# OVERLAPS H-Level-/₂ #-}

instance
  Extensional-/₂-map
    : ∀ {ℓ ℓ′ ℓ″ ℓr} {A : Type ℓ} {R : A → A → Type ℓ′} {B : Type ℓ″}
      ⦃ sf : Extensional (A → B) ℓr ⦄ ⦃ B-set : H-Level 2 B ⦄
    → Extensional (A / R → B) ℓr
  Extensional-/₂-map ⦃ sf ⦄ .Pathᵉ f g = sf .Pathᵉ (f ∘ ⦋_⦌) (g ∘ ⦋_⦌)
  Extensional-/₂-map ⦃ sf ⦄ .reflᵉ f = sf .reflᵉ (f ∘ ⦋_⦌)
  Extensional-/₂-map ⦃ sf ⦄ .idsᵉ .to-path h = fun-ext $ elim! (sf .idsᵉ .to-path h $ₚ_)
  Extensional-/₂-map ⦃ sf ⦄ .idsᵉ .to-path-over p =
    is-prop→pathᴾ (λ i → Pathᵉ-is-of-hlevel 1 sf (hlevel 2)) _ p

module @0 _ {R : Corr 2 (A , A) ℓ} (congr : is-congruence R) where
  open is-congruence congr
  open Equivalence equivalence

  Code : A → A / R → Prop ℓ
  Code x = /₂.elim hlevel! (λ y → el! (R x y)) λ y z r →
    ext (_∙ r , _∙ r ⁻¹)

  encode : ∀ x y (p : ⦋ x ⦌ ＝ y) → ⌞ Code x y ⌟
  encode x _ p = subst (λ y → ⌞ Code x y ⌟) p refl

  decode : ∀ x y (p : ⌞ Code x y ⌟) → ⦋ x ⦌ ＝ y
  decode = elim! ∘ glue/

  effective : R x y
            ≃ ⦋ x ⦌ ＝ ⦋ y ⦌
  effective {x} {y} = prop-extₑ! (decode x ⦋ y ⦌) (encode x ⦋ y ⦌)

instance
  Reflects-⦋-⦌=⦋-⦌ : ⦃ r : Reflects (R a b) true ⦄ → Reflects (Path (A / R) ⦋ a ⦌ ⦋ b ⦌) true
  Reflects-⦋-⦌=⦋-⦌ = Reflects.dmap (glue/ _ _) (λ f _ → ⊥.rec $ f $ true!) auto

  Reflects-⦋-⦌≠⦋-⦌
    : ⦃ c : is-congruence R ⦄ ⦃ a≠b : Reflects (a ＝ b) false ⦄ ⦃ r : Reflects (R a b) false ⦄
    → Reflects (Path (A / R) ⦋ a ⦌ ⦋ b ⦌) false
  Reflects-⦋-⦌≠⦋-⦌ ⦃ a≠b ⦄ = Reflects.dmap
    (glue/ _ _ ∘ snd)
    (λ f p → ⊥.rec (¬-so-false (true→so! $ effective auto ⁻¹ $ p)))
    (Reflects-× ⦃ a≠b ⦄)

  /₂-is-discrete
    : ⦃ c : is-congruence R ⦄ ⦃ d : ∀ {x y} → Dec (R x y) ⦄
    → is-discrete (A / R)
  /₂-is-discrete {A} {R} {x = x/} {y = y/} = elim! {P = λ x → (y : A / R) → Dec (x ＝ y)}
    (λ x y → Dec.dmap (glue/ x y) (λ f p → ⊥.rec $ f $ effective auto ⁻¹ $ p) auto)
    x/ y/
