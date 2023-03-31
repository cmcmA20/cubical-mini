{-# OPTIONS --safe #-}
module Cubical.Data.Char.Properties where

open import Agda.Builtin.Char.Properties renaming (primCharToNatInjective to toℕ-injective)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding

open import Cubical.Data.Char.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Equality using (eqToPath; pathToEq) renaming (_≡_ to _≣_)

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Negation

private variable
  c c₁ c₂ : Char

≈⇒≡ : c₁ ≈ c₂ → c₁ ≡ c₂
≈⇒≡ = eqToPath ∘ toℕ-injective _ _ ∘ pathToEq

≉⇒≢ : c₁ ≉ c₂ → ¬ (c₁ ≡ c₂)
≉⇒≢ f p = f (cong toℕ p)

discreteChar : Discrete Char
discreteChar c₁ c₂ = mapDec ≈⇒≡ ≉⇒≢ (discreteℕ (toℕ c₁) (toℕ c₂))

-- TODO injEmbedding can be refactored to not use ua
@0 isSetChar : isSet Char
isSetChar = Embedding-into-isSet→isSet (toℕ , injEmbedding isSetℕ ≈⇒≡) isSetℕ
