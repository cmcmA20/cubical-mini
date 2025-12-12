{-# OPTIONS --safe #-}
module Foundations.Notation.Membership where

open import Foundations.Notation.Logic
open import Foundations.Notation.Underlying
open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Composition
open import Foundations.Notation.Duality
open import Foundations.Prim.Type
open import Foundations.Prim.Equiv
open import Foundations.Pi.Base
open import Foundations.Sigma.Base

open import Agda.Builtin.Unit

-- generalizing powerset membership
record Membership {ℓ ℓe} (A : Type ℓe) (ℙA : Type ℓ) ℓm : Type (ℓ ⊔ ℓsuc (ℓe ⊔ ℓm)) where
  infix 30 _∈_
  field _∈_ : A → ℙA → Type ℓm
open Membership ⦃ ... ⦄ public
{-# DISPLAY Membership._∈_ _ a b = a ∈ b #-}

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ′ ℓ″ ℓ‴ ℓa ℓb ℓp : Level
  A : Type ℓa
  ℙA₁ : Type ℓ₁
  ℙA₂ : Type ℓ₂
  ℙA₃ : Type ℓ₃

infix 20 _⊆_ _≬_
_⊆_
  : ⦃ m₁ : Membership A ℙA₁ ℓ′ ⦄ ⦃ m₂ : Membership A ℙA₂ ℓ″ ⦄
  → ℙA₁ → ℙA₂ → Type (level-of-type A ⊔ ℓ′ ⊔ ℓ″)
_⊆_ {A} S T = ∀[ a ꞉ A ] (a ∈ S ⇒ a ∈ T)

-- TODO making these and below into (incoherent) instances breaks Cat.Univalent

Refl-⊆ : ⦃ m₁ : Membership A ℙA₁ ℓ‴ ⦄
       → Refl {A = ℙA₁} _⊆_
Refl-⊆ .refl = id

-- TODO Comp
Trans-⊆ : ⦃ m₁ : Membership A ℙA₁ ℓ‴ ⦄
        → Trans {A = ℙA₁} _⊆_
Trans-⊆ ._∙_ i o = o ∘ i

-- overlap
_≬_
  : ⦃ m₁ : Membership A ℙA₁ ℓ′ ⦄ ⦃ m₂ : Membership A ℙA₂ ℓ″ ⦄
  → ℙA₁ → ℙA₂ → Type (level-of-type A ⊔ ℓ′ ⊔ ℓ″)
_≬_ {A} S T = Σ[ a ꞉ A ] (a ∈ S × a ∈ T)

-- set-equivalence
_≈_
  : ⦃ m₁ : Membership A ℙA₁ ℓ′ ⦄ ⦃ m₂ : Membership A ℙA₂ ℓ″ ⦄
  → ℙA₁ → ℙA₂ → Type (level-of-type A ⊔ ℓ′ ⊔ ℓ″)
S ≈ T = S ⊆ T × T ⊆ S

Refl-≈ : ⦃ m₁ : Membership A ℙA₁ ℓ′ ⦄
       → Refl {A = ℙA₁} _≈_
Refl-≈ .refl = refl , refl

Trans-≈ : ⦃ m₁ : Membership A ℙA₁ ℓ‴ ⦄
        → Trans {A = ℙA₁} _≈_
Trans-≈ ._∙_ i o = i .fst ∙ o .fst , o .snd ∙ i .snd

-- doesn't work very well as is
Comp-≈ : ⦃ m₁ : Membership A ℙA₁ ℓ′ ⦄
         ⦃ m₂ : Membership A ℙA₂ ℓ″ ⦄
         ⦃ m₃ : Membership A ℙA₃ ℓ‴ ⦄
        → Comp {A = ℙA₁} {B = ℙA₂} {C = ℙA₃}
               (_≈_ ⦃ m₁ = m₁ ⦄ ⦃ m₂ = m₂ ⦄)
               (_≈_ ⦃ m₁ = m₂ ⦄ ⦃ m₂ = m₃ ⦄)
               (_≈_ ⦃ m₁ = m₁ ⦄ ⦃ m₂ = m₃ ⦄)
Comp-≈ ._∙_ i o = i .fst ∙ o .fst , o .snd ∙ i .snd

Dual-≈ : {A : Type ℓ} ⦃ m₁ : Membership A ℙA₁ ℓ′ ⦄ ⦃ m₂ : Membership A ℙA₂ ℓ″ ⦄
       → Dual (_≈_ ⦃ m₁ = m₁ ⦄)  (_≈_ ⦃ m₁ = m₂ ⦄)
Dual-≈ ._ᵒᵖ (l , r) = r , l

-- TODO subbag relation requires some notion of generalized injection/embedding

-- bag-equivalence
_≈↔_
  : ⦃ m₁ : Membership A ℙA₁ ℓ′ ⦄ ⦃ m₂ : Membership A ℙA₂ ℓ″ ⦄
  → ℙA₁ → ℙA₂ → Type (level-of-type A ⊔ ℓ′ ⊔ ℓ″)
_≈↔_ {A} S T = ∀[ a ꞉ A ] (a ∈ S ≃ a ∈ T)

-- TODO bag-equiv symmetry/reflexivity/transitivity requires properties of equivs

≈↔→≈ : ⦃ m₁ : Membership A ℙA₁ ℓ′ ⦄ ⦃ m₂ : Membership A ℙA₂ ℓ″ ⦄
     → {S : ℙA₁} {T : ℙA₂}
     → S ≈↔ T → S ≈ T
≈↔→≈ beq = (beq $_) , (equiv-backward beq)

record Intersection {ℓ ℓ′ ℓ″} (A : Type ℓ) (B : Type ℓ′) (R : Type ℓ″) : Typeω where
  infixr 22 _∩_
  field _∩_ : A → B → R
open Intersection ⦃ ... ⦄ public
{-# DISPLAY Intersection._∩_ _ a b = a ∩ b #-}

record Union {ℓ ℓ′ ℓ″} (A : Type ℓ) (B : Type ℓ′) (R : Type ℓ″) : Typeω where
  infixr 21 _∪_
  field _∪_ : A → B → R
open Union ⦃ ... ⦄ public
{-# DISPLAY Union._∪_ _ a b = a ∪ b #-}


instance
  Membership-pow
    : {A : Type ℓa} {P : Type ℓp} ⦃ u : Underlying P ⦄
    → Membership A (A → P) (u .ℓ-underlying)
  Membership-pow ._∈_ x S = ⌞ S x ⌟
  {-# OVERLAPPABLE Membership-pow #-}

  Intersection-pow
    : {A : Type ℓa} ⦃ ua : Underlying A ⦄
      {B : Type ℓb} ⦃ ub : Underlying B ⦄
      {P : Type ℓp} {X : Type ℓ}
      ⦃ un : ×-notation {ℓ′ = ℓ″} (Type (ua .ℓ-underlying)) (Type (ub .ℓ-underlying)) P ⦄
      ⦃ _ : ∀ {x y} → un .×-notation.Constraint x y ⦄
    → Intersection (X → A) (X → B) (X → P)
  Intersection-pow ._∩_ S T x = ⌞ S x ⌟ × ⌞ T x ⌟
  {-# OVERLAPPABLE Intersection-pow #-}

