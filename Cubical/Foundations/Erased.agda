-- "Compiling Programs with Erased Univalence"
-- by Andreas Abel, Nils Anders Danielsson and Andrea Vezzosi
{-# OPTIONS --safe #-}
module Cubical.Foundations.Erased where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥

open import Cubical.Relation.Nullary.Base

private variable
  ℓ ℓ′ : Level
  @0 A : Type ℓ
  @0 B : Type ℓ′
  @0 x y : A

record Erased (@0 A : Type ℓ) : Type ℓ where
  constructor [_]
  field @0 erased : A
open Erased

[]-cong : Erased (x ≡ y) → [ x ] ≡ [ y ]
[]-cong [ p ] = λ i → [ p i ]

substᴱ : (B : @0 A → Type ℓ′) → (@0 p : x ≡ y) → B x → B y
substᴱ B p = subst (λ z → B (z .erased)) ([]-cong [ p ])

-- isContrᴱ : Type ℓ → Type ℓ
-- isContrᴱ A = Σ[ x ∈ A ] Erased (∀ y → x ≡ y)

-- record isEquivᴱ {A : Type ℓ} {B : Type ℓ′} (f : A → B) : Type (ℓ-max ℓ ℓ′) where
--   no-eta-equality
--   field
--     equiv-proofᴱ : (y : B) → isContrᴱ (fiber f y)
-- open isEquivᴱ

-- _≃ᴱ_ : (A : Type ℓ) (B : Type ℓ′) → Type (ℓ-max ℓ ℓ′)
-- A ≃ᴱ B = Σ (A → B) isEquivᴱ

-- equivFunᴱ : {A : Type ℓ} {B : Type ℓ′} → A ≃ᴱ B → A → B
-- equivFunᴱ = fst

-- equivInvᴱ : {A : Type ℓ} {B : Type ℓ′} → A ≃ᴱ B → B → A
-- equivInvᴱ e y = e .snd .equiv-proofᴱ y .fst .fst
