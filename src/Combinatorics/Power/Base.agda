{-# OPTIONS --safe #-}
module Combinatorics.Power.Base where

open import Meta.Prelude
open import Meta.Extensionality

open import Structures.n-Type

open import Data.Empty as ⊥
open import Data.Sum
open import Data.Truncation.Propositional as ∥-∥₁
open import Data.Unit.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  X : Type ℓ
  x y : X
  m n k : HLevel

ℙ : Type ℓ → Type (ℓsuc ℓ)
ℙ X = X → Prop _

private variable A B : ℙ X

subst-∈ : (A : ℙ X) {x y : X} → x ＝ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

⊆-refl : (A : ℙ X) → A ⊆ A
⊆-refl _ = refl

@0 ℙ-ext : A ⊆ B → B ⊆ A → A ＝ B
ℙ-ext A⊆B B⊆A = ext λ _ → A⊆B , B⊆A

single : ⦃ X-set : H-Level 2 X ⦄ → X → ℙ X
single x t = el! (x ＝ t)

instance
  Intersection-n-Type
    : Intersection (X → n-Type ℓ n) (X → n-Type ℓ′ n) (X → n-Type (ℓ ⊔ ℓ′) n)
  Intersection-n-Type ._∩_ A B x = el! ((x ∈ A) × (x ∈ B))

  Union-n-Type
    : ⦃ _ : 2 ≤ʰ n ⦄
    → Union (X → n-Type ℓ n) (X → n-Type ℓ′ n) (X → n-Type (ℓ ⊔ ℓ′) n)
  Union-n-Type ⦃ s≤ʰs (s≤ʰs _) ⦄ ._∪_ A B x = el! ((x ∈ A) ⊎ (x ∈ B))
  {-# OVERLAPS Union-n-Type #-}

  Union-Prop
    : Union (X → Prop ℓ) (X → Prop ℓ′) (X → Prop (ℓ ⊔ ℓ′))
  Union-Prop ._∪_ A B x = el! ((x ∈ A) ⊎₁ (x ∈ B))
  {-# OVERLAPPING Union-Prop #-}

instance
  ⊤-Pow : ⊤-notation (ℙ X)
  ⊤-Pow .⊤ _ = ⊤

  ⊥-Pow : ⊥-notation (ℙ X)
  ⊥-Pow .⊥ _ = ⊥

⊥⊆ : ⊥ ⊆ A
⊥⊆ ()

@0 ⊆⊥→⊥ : A ⊆ ⊥ → A ＝ ⊥
⊆⊥→⊥ {A} p = ℙ-ext p (⊥⊆ {A = A})

⊆⊤ : A ⊆ ⊤
⊆⊤ = _
