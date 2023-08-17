{-# OPTIONS --safe #-}
module Correspondences.Decidable where

open import Foundations.Base

open import Correspondences.Base public
open import Correspondences.Classical

open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Nat.Base

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  n : HLevel

dec→essentially-classical : Dec A → Essentially-classical A
dec→essentially-classical = essentially-classical-η ∘ Dec.rec
  (λ a _ → a)
  (λ ¬a f → ⊥.rec (f ¬a))

decide : ⦃ d : Dec A ⦄ → Dec A
decide ⦃ d ⦄ = d

×-decision : Dec A → Dec B → Dec (A × B)
×-decision da db .does = da .does and db .does
×-decision (no ¬a) db .proof = ofⁿ $ ¬a ∘ fst
×-decision (yes a) (no ¬b) .proof = ofⁿ $ ¬b ∘ snd
×-decision (yes a) (yes b) .proof = ofʸ (a , b)

fun-decision : Dec A → Dec B → Dec (A → B)
fun-decision da db .does = not (da .does) or db .does
fun-decision (no ¬a) db .proof = ofʸ $ λ a → absurd (¬a a)
fun-decision (yes a) (no ¬b) .proof = ofⁿ $ ¬b ∘ (_$ a)
fun-decision (yes a) (yes b) .proof = ofʸ λ _ → b

¬-decision : Dec A → Dec (¬ A)
¬-decision da .does = not (da .does)
¬-decision (yes a) .proof = ofⁿ (_$ a)
¬-decision (no ¬a) .proof = ofʸ ¬a


-- Decidability of a homogeneous predicate
Decidable : Pred _ (Corr n ℓ A)
Decidable P = Π[ Dec ∘ⁿ P ]

-- Homogeneous decision procedure
DProc
  : (arity : ℕ) (ℓ′ : Level)
    {ℓ : Level} (A : Type ℓ)
  → Type (Levelₓ ℓ 0ℓ arity)
DProc arity ℓ′ A = functionₓ arity A Bool

DProc⁰ = DProc 0
DProc¹ = DProc 1
DProc² = DProc 2
DProc³ = DProc 3

-- Evidence of a (homogeneous) correspondence `P` being reflected by a decision procedure
Reflects : Corr n ℓ A → DProc n ℓ A → Type (level-of-type A ⊔ ℓ)
Reflects {n = 0}     {A} P d = Lift (level-of-type A) (Reflects¹ P d)
Reflects {n = suc n} {A} P d = Π[ (λ (x : A) → Reflects (P x) (d x)) ]

reflects→decidable
  : {A : Type ℓᵃ} {P : Corr n ℓ A} {d : DProc n ℓ A}
  → Reflects P d → Decidable P
reflects→decidable {n = 0} {d} p .lower = d because lower p
reflects→decidable {n = 1} {d} f x = d x because lower (f x)
reflects→decidable {n = suc (suc _)} f x = reflects→decidable (f x)
