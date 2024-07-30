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
  ℓˣ ℓ ℓ′ ℓ″ : Level
  X : Type ℓˣ
  x y : X
  m n k : HLevel

ℙ : Type ℓˣ → (ℓ : Level) → Type (ℓˣ ⊔ ℓsuc ℓ)
ℙ X ℓ = X → Prop ℓ

private variable A B : ℙ X ℓ

subst-∈ : (A : ℙ X ℓ) {x y : X} → x ＝ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

⊆-refl : (A : ℙ X ℓ) → A ⊆ A
⊆-refl _ = id

⊆-trans : (A : ℙ X ℓ) (B : ℙ X ℓ′) (C : ℙ X ℓ″) → A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans _ _ _ ab bc = bc ∘ ab

@0 ℙ-ext : A ⊆ B → B ⊆ A → A ＝ B
ℙ-ext A⊆B B⊆A = ext λ _ → A⊆B , B⊆A

single : ⦃ X-set : H-Level 2 X ⦄ → X → ℙ X (level-of-type X)
single x t = el! (x ＝ t)

⋁_ : {I : 𝒰 ℓ} → (I → ℙ X ℓ) → ℙ X ℓ
⋁_ {I} F x = el! (∃[ i ꞉ I ] x ∈ F i)

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
  ⊤-Pow : ⊤-notation (ℙ X ℓ)
  ⊤-Pow .⊤ _ = ⊤

  ⊥-Pow : ⊥-notation (ℙ X ℓ)
  ⊥-Pow .⊥ _ = ⊥

⊥⊆ : _⊆_ ⦃ m₁ = Membership-pow {P = Prop ℓ′} ⦄ ⊥ A
⊥⊆ ()

@0 ⊆⊥→⊥ : A ⊆ ⊥ → A ＝ ⊥
⊆⊥→⊥ {A} p = ℙ-ext p (⊥⊆ {A = A})

⊆⊤ : _⊆_ ⦃ m₂ = Membership-pow {P = Prop ℓ′} ⦄ A ⊤
⊆⊤ = _

-- total space

𝕋 : ℙ X ℓ → 𝒰 (level-of-type X ⊔ ℓ)
𝕋 {X} A = Σ[ x ꞉ X ] x ∈ A

ℙ→fam : {X : Type ℓˣ} {Y : Type ℓ′}
      → (X → Y) → ℙ X ℓ → Σ[ I ꞉ 𝒰 (ℓ ⊔ level-of-type X) ] (I → Y)
ℙ→fam m S = 𝕋 S , m ∘ fst
