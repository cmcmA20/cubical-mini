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
  ℓˣ ℓʸ ℓ ℓ′ ℓ″ : Level
  X : Type ℓˣ
  Y : Type ℓʸ
  x y : X
  m n k : HLevel

ℙ : {ℓˣ : Level} → Type ℓˣ → (ℓ : Level) → Type (ℓˣ ⊔ ℓsuc ℓ)
ℙ X ℓ = X → Prop ℓ

private variable A B : ℙ X ℓ

subst-∈ : (A : ℙ X ℓ) {x y : X} → x ＝ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

instance
  Refl-⊆ : Refl {A = ℙ X ℓ} _⊆_
  Refl-⊆ .refl = refl
  {-# OVERLAPPING Refl-⊆ #-}

  Trans-⊆ : Trans {A = ℙ X ℓ} {B = ℙ X ℓ′} {C = ℙ X ℓ″} _⊆_ _⊆_ _⊆_
  Trans-⊆ ._∙_ S T = S ∙ T
  {-# OVERLAPPING Trans-⊆ #-}

@0 ℙ-ext : A ⊆ B → B ⊆ A → A ＝ B
ℙ-ext A⊆B B⊆A = ext λ _ → A⊆B , B⊆A

single : ⦃ X-set : H-Level 2 X ⦄ → X → ℙ X (level-of-type X)
single x t = el! (x ＝ t)

⋁_ : {I : 𝒰 ℓ} → (I → ℙ X ℓ) → ℙ X ℓ
⋁_ {I} F x = el! (∃[ i ꞉ I ] x ∈ F i)

ℙ-map : {X X′ : Type ℓˣ} → (X → X′) → ℙ X ℓ → ℙ X′ (ℓˣ ⊔ ℓ)
ℙ-map {X} f px x′ = el! (∃[ x ꞉ X ] (x′ ＝ f x) × ⌞ x ∈ px ⌟)

ℙ-ctramap : (Y → X) → ℙ X ℓ → ℙ Y ℓ
ℙ-ctramap f px = px ∘ f

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

  ⊤-Pow : ⊤-notation (ℙ X ℓ)
  ⊤-Pow .⊤ _ = ⊤

  ⊥-Pow : ⊥-notation (ℙ X ℓ)
  ⊥-Pow .⊥ _ = ⊥

⊥⊆ : {A : ℙ X ℓ} → the (ℙ X ℓ′) ⊥ ⊆ A
⊥⊆ ()

@0 ⊆⊥→⊥ : A ⊆ ⊥ → A ＝ ⊥
⊆⊥→⊥ {A} p = ℙ-ext p (⊥⊆ {A = A})

⊆⊤ : {A : ℙ X ℓ} → A ⊆ the (ℙ X ℓ′) ⊤
⊆⊤ = _

ℙ-inl : {A B C : ℙ X ℓ} → C ⊆ A → C ⊆ A ∪ B
ℙ-inl ca cx = ∣ inl (ca cx) ∣₁

ℙ-inr : {A B C : ℙ X ℓ} → C ⊆ B → C ⊆ A ∪ B
ℙ-inr cb cx = ∣ inr (cb cx) ∣₁

∪-⊆ : {A B C : ℙ X ℓ} → A ⊆ C → B ⊆ C → A ∪ B ⊆ C
∪-⊆ ac bc = elim! [ ac , bc ]ᵤ

-- FIXME what's the point?
𝕋→carrier : (A : ℙ X ℓ) → Σ[ A ] → X
𝕋→carrier _ = fst

ℙ→fam : {X : Type ℓˣ} {Y : Type ℓ′}
      → (X → Y) → ℙ X ℓ → Σ[ I ꞉ 𝒰 (ℓ ⊔ ℓˣ) ] (I → Y)
ℙ→fam m S = Σ[ S ] , m ∘ fst
