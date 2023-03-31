{-# OPTIONS --safe #-}
module Cubical.Relation.Nullary.AnonymousExistence where

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Functions.Fixpoint

open import Cubical.Data.Empty as ⊥
open import Cubical.Truncation.Propositional.Base

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Negation

private
  variable
    ℓ ℓ′ : Level
    A : Type ℓ

SplitSupport : Type ℓ → Type ℓ
SplitSupport A = ∥ A ∥₁ → A

Collapsible : Type ℓ → Type ℓ
Collapsible A = Σ[ f ꞉ (A → A) ] 2-Constant f

Populated ⟪_⟫ : Type ℓ → Type ℓ
Populated A = (f : Collapsible A) → Fixpoint (f .fst)
⟪_⟫ = Populated

PStable : Type ℓ → Type ℓ
PStable A = ⟪ A ⟫ → A

Separated : Type ℓ → Type ℓ
Separated = onAllPaths Stable

HSeparated : Type ℓ → Type ℓ
HSeparated = onAllPaths SplitSupport

Collapsible≡ : Type ℓ → Type ℓ
Collapsible≡ = onAllPaths Collapsible

PStable≡ : Type ℓ → Type ℓ
PStable≡ = onAllPaths PStable

-- isPropPopulated : isProp (Populated A)
-- isPropPopulated = isPropΠ λ x → 2-Constant→isPropFixpoint (x .fst) (x .snd)

-- isPropHSeparated : isProp (HSeparated A)
-- isPropHSeparated f g i x y a = HSeparated→isSet f x y (f x y a) (g x y a) i

-- separatedΣ : {B : A → Type ℓ′} → Separated A → ((a : A) → Separated (B a)) → Separated (Σ A B)
-- separatedΣ {B = B} sepA sepB (a , b) (a' , b') p = ΣPathTransport→PathΣ _ _ (pA , pB)
--   where
--     pA : a ≡ a'
--     pA = sepA a a' (λ q → p (λ r → q (cong fst r)))

--     pB : subst B pA b ≡ b'
--     pB = sepB _ _ _ (λ q → p (λ r → q (cong (λ r' → subst B r' b)
--                                 (Separated→isSet sepA _ _ pA (cong fst r)) ∙ snd (PathΣ→ΣPathTransport _ _ r))))
