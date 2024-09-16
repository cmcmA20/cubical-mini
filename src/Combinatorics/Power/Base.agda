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

  Comp-⊆ : Comp {A = ℙ X ℓ} {B = ℙ X ℓ′} {C = ℙ X ℓ″} _⊆_ _⊆_ _⊆_
  Comp-⊆ ._∙_ S T = S ∙ T
  {-# OVERLAPPING Comp-⊆ #-}

single : ⦃ X-set : H-Level 2 X ⦄ → X → ℙ X (level-of-type X)
single x t = el! (x ＝ t)

instance
  ∃-ℙ
    : {A : Type ℓ′} ⦃ ua : Underlying A ⦄
    → ∃-notation A (ℙ X ℓ) (ℙ X (ℓ ⊔ ua .ℓ-underlying))
  ∃-ℙ .∃-notation.∃ A′ F x = el! (∃[ i ꞉ ⌞ A′ ⌟ ] x ∈ F i)

  Intersection-pow-n-Type
    : Intersection (X → n-Type ℓ n) (X → n-Type ℓ′ n) (X → n-Type (ℓ ⊔ ℓ′) n)
  Intersection-pow-n-Type ._∩_ A B x = el! ((x ∈ A) × (x ∈ B))

  Union-pow-n-Type
    : ⦃ _ : 2 ≤ʰ n ⦄
    → Union (X → n-Type ℓ n) (X → n-Type ℓ′ n) (X → n-Type (ℓ ⊔ ℓ′) n)
  Union-pow-n-Type ⦃ s≤ʰs (s≤ʰs _) ⦄ ._∪_ A B x = el! ((x ∈ A) ⊎ (x ∈ B))
  {-# OVERLAPS Union-pow-n-Type #-}

  Union-ℙ
    : Union (ℙ X ℓ) (ℙ X ℓ′) (ℙ X (ℓ ⊔ ℓ′))
  Union-ℙ ._∪_ A B x = el! ((x ∈ A) ⊎₁ (x ∈ B))
  {-# OVERLAPPING Union-ℙ #-}

  ⊤-ℙ : ⊤-notation (ℙ X ℓ)
  ⊤-ℙ .⊤ _ = ⊤

  ⊥-ℙ : ⊥-notation (ℙ X ℓ)
  ⊥-ℙ .⊥ _ = ⊥

⊥⊆ : {A : ℙ X ℓ} → the (ℙ X ℓ′) ⊥ ⊆ A
⊥⊆ ()

@0 ⊆⊥→⊥ : A ⊆ ⊥ → A ＝ ⊥
⊆⊥→⊥ p = ext λ _ → p , λ()

⊆⊤ : {A : ℙ X ℓ} → A ⊆ the (ℙ X ℓ′) ⊤
⊆⊤ = _

ℙ-inl : {A B C : ℙ X ℓ} → C ⊆ A → C ⊆ A ∪ B
ℙ-inl ca cx = ∣ inl (ca cx) ∣₁

ℙ-inr : {A B C : ℙ X ℓ} → C ⊆ B → C ⊆ A ∪ B
ℙ-inr cb cx = ∣ inr (cb cx) ∣₁

∪-⊆ : {A B C : ℙ X ℓ} → A ⊆ C → B ⊆ C → A ∪ B ⊆ C
∪-⊆ ac bc = elim! [ ac , bc ]ᵤ

ℙ→fam : {X : Type ℓˣ} {Y : Type ℓʸ}
      → (X → Y) → ℙ X ℓ
      → Σ[ I ꞉ 𝒰 (ℓ ⊔ ℓˣ) ] (I → Y)
ℙ→fam m S = Σ[ S ] , m ∘ fst
