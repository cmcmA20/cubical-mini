{-# OPTIONS --safe #-}
module Structures.Base where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Sigma
open import Foundations.Isomorphism
open import Foundations.Univalence

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  S T : Type ℓ → Type ℓ′

record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟          : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ using (⌞_⌟) public
open Underlying using (ℓ-underlying)

record Structure {ℓ₁ ℓ₂} (ℓ₃ : _)
  (S : Type ℓ₁ → Type ℓ₂) : Type (ℓsuc (ℓ₁ ⊔ ℓ₃) ⊔ ℓ₂) where

  constructor HomT→Str
  field
    is-hom : (A B : Σ _ S) → (A .fst ≃ B .fst) → Type ℓ₃

open Structure public

Type-with : Structure ℓ″ S → Type _
Type-with {S} _ = Σ _ S

@0 is-univalent : Structure ℓ S → Type _
is-univalent {S} ι =
  ∀ {X Y}
  → (f : X .fst ≃ Y .fst)
  → ι .is-hom X Y f ≃ ＜ X .snd ／ (λ i → S (ua f i)) ＼ Y .snd ＞

-- σ-homomorphic equivalences
_≃[_]_ : Σ _ S → Structure ℓ S → Σ _ S → Type _
A ≃[ σ ] B = Σ[ f ꞉ A .fst ≃ B .fst ] (σ .is-hom A B f)

private variable
  σ : Structure ℓ S

-- The Structure Identity Principle says that, if `S` is a `univalent
-- structure`, then the path space of `Σ S` is equivalent to the space of
-- S-homomorphic equivalences of types. Using groups as a grounding
-- example: identification of groups is group isomorphism.
@0 SIP : is-univalent σ → {X Y : Σ _ S}
       → (X ≃[ σ ] Y) ≃ (X ＝ Y)
SIP {S} {σ} is-univ {X} {Y} =
  X ≃[ σ ] Y                                                            ≃⟨⟩
  (Σ[ e ꞉ X .fst ≃  Y .fst ] (σ .is-hom X Y e))                         ≃⟨ Σ-ap (ua , univalence⁻¹) is-univ ⟩
  (Σ[ p ꞉ X .fst ＝ Y .fst ] ＜ X .snd ／ (λ i → S (p i)) ＼ Y .snd ＞) ≃⟨ Iso→Equiv Σ-PathP-iso ⟩
  X ＝ Y                                                                ≃∎

@0 sip : is-univalent σ → {X Y : Σ _ S} → (X ≃[ σ ] Y) → (X ＝ Y)
sip is-univ = SIP is-univ .fst

-- TODO common structures

-- instance
--   mk-type-with-str : {X : Type ℓ} → ⦃ S X ⦄ → Type-with ℓ S
--   mk-type-with-str ⦃ (s) ⦄ = _ , s

-- An S-structure should have a notion of S-homomorphism, or rather S-isomorphism.
-- This will be implemented by a function ι : StrEquiv S ℓ'
-- that gives us for any two types with S-structure (X , s) and (Y , t) a family:
--    ι (X , s) (Y , t) : (X ≃ Y) → Type ℓ″

-- Str-equiv : (S : Type ℓ → Type ℓ″) (ℓ′ : Level) → Type (ℓsuc (ℓ ⊔ ℓ′) ⊔ ℓ″)
-- Str-equiv {ℓ} S ℓ′ = (A B : Type-with ℓ S) → type A ≃ type B → Type ℓ′

-- An S-structure may instead be equipped with an action on equivalences, which will
-- induce a notion of S-homomorphism

-- Equiv-action : (S : Type ℓ → Type ℓ″) → Type (ℓsuc ℓ ⊔ ℓ″)
-- Equiv-action {ℓ} S = {X Y : Type ℓ} → X ≃ Y → S X ≃ S Y

-- Equiv-action→Str-equiv : {S : Type ℓ → Type ℓ″} → Equiv-action S → Str-equiv S ℓ″
-- Equiv-action→Str-equiv α (X , s) (Y , t) e = equiv-forward (α e) s ＝ t



_on-paths-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-paths-of A = Π[ x ꞉ A ] Π[ y ꞉ A ] S (x ＝ y)
