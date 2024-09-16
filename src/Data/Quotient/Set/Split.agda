{-# OPTIONS --safe #-}
module Data.Quotient.Set.Split where

open import Meta.Prelude

open import Data.Quotient.Set.Base as /₂
open import Data.Quotient.Set.Path

open import Functions.Surjection

private variable ℓ ℓ′ : Level

record is-split-congruence
  {A : Type ℓ} {R : A → A → Type ℓ′}
  (co : is-congruence R) : Type (ℓ ⊔ ℓ′) where
  open is-congruence co
  open Equivalence equivalence

  field
    has-is-set : is-set A
    normalise  : A → A
    represents : ∀ x → Erased (R x (normalise x))
    respects   : ∀ x y → R x y → normalise x ＝ normalise y

  private instance
    A-set : ∀ {n} → H-Level (2 + n) A
    A-set = hlevel-basic-instance 2 has-is-set

  splitting : Split-surjectiveᴱ ⦋_⦌
  splitting = /₂.elim (λ _ → hlevel 2)
    (λ a → normalise a , erase (glue/ _ _ (represents a .erased ⁻¹)))
    λ a b r → respects a b r ,ₚ prop!

  choose : A / R → A
  choose x = splitting x .fst

  normalise-idem : ∀ x → Erased (normalise (normalise x) ＝ normalise x)
  normalise-idem x .erased = respects _ _ (represents x .erased ⁻¹)

  reflects : ∀ x y → normalise x ＝ normalise y → Erased (R x y)
  reflects x y p .erased
    = represents x .erased
    ∙ transport (λ i → R (normalise x) (p i)) refl
    ∙ represents y .erased ⁻¹

open is-split-congruence

split-surjectiveᴱ→is-split-congruence
  : ∀{ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′}
    ⦃ _ : H-Level 2 A ⦄ (co : is-congruence R)
  → Split-surjectiveᴱ {B = A / R} ⦋_⦌
  → is-split-congruence co
split-surjectiveᴱ→is-split-congruence co f .has-is-set = hlevel 2
split-surjectiveᴱ→is-split-congruence co f .normalise x = f ⦋ x ⦌ .fst
split-surjectiveᴱ→is-split-congruence co f .represents x .erased =
  effective co ⁻¹ $ f ⦋ x ⦌ .snd .erased ⁻¹
split-surjectiveᴱ→is-split-congruence co f .respects x y p =
  ap (fst ∘ f) (glue/ _ _ p)
