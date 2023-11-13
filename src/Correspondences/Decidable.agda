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
dec→essentially-classical = Dec.rec
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

lift-decision : Dec A → Dec (Lift ℓ A)
lift-decision da .does = da .does
lift-decision (yes a) .proof = ofʸ (lift a)
lift-decision (no ¬a) .proof = ofⁿ (¬a ∘ lower)

instance
  universe-decision : Dec (Type ℓ)
  universe-decision = yes (Lift _ ⊤)


-- Decidability of a predicate
Decidable : (arity : ℕ) {ls : Levels arity} {As : Types arity ls} → Pred _ (Corr arity ℓ As)
Decidable arity P = Πⁿ[ mapⁿ arity Dec P ]

Decidable¹ : {ls : Levels _} {As : Types _ ls} → Pred _ (Corr 1 ℓ As)
Decidable¹ = Decidable 1

Decidable² : {ls : Levels _} {As : Types _ ls} → Pred _ (Corr 2 ℓ As)
Decidable² = Decidable 2

Decidable³ : {ls : Levels _} {As : Types _ ls} → Pred _ (Corr 3 ℓ As)
Decidable³ = Decidable 3

Decidable⁴ : {ls : Levels _} {As : Types _ ls} → Pred _ (Corr 4 ℓ As)
Decidable⁴ = Decidable 4

-- Decision procedure
DProc
  : (arity : ℕ)
    {ls : Levels arity} (As : Types _ ls)
  → Type (ℓsup arity ls)
DProc arity As = Arrows arity As Bool

DProc⁰ = DProc 0
DProc¹ = DProc 1
DProc² = DProc 2
DProc³ = DProc 3
DProc⁴ = DProc 4
DProc⁵ = DProc 5

-- Evidence of a correspondence `P` being reflected by a decision procedure
Reflects : (arity : ℕ) {ls : Levels arity} {As : Types _ ls} → Corr _ ℓ As → DProc _ As → Type (ℓ ⊔ ℓsup _ ls)
Reflects 0                           P d = Reflects⁰ P d
Reflects 1             {As = A}      P d = Π[ x ꞉ A ] Reflects _ (P x) (d x)
Reflects (suc (suc _)) {As = A , As} P d = Π[ x ꞉ A ] Reflects _ (P x) (d x)

Reflects¹ : {ls : Levels 1} {As : Types _ ls} → Corr _ ℓ As → DProc _ As → Type _
Reflects¹ = Reflects 1

Reflects² : {ls : Levels 2} {As : Types _ ls} → Corr _ ℓ As → DProc _ As → Type _
Reflects² = Reflects 2

Reflects³ : {ls : Levels 3} {As : Types _ ls} → Corr _ ℓ As → DProc _ As → Type _
Reflects³ = Reflects 3

Reflects⁴ : {ls : Levels 4} {As : Types _ ls} → Corr _ ℓ As → DProc _ As → Type _
Reflects⁴ = Reflects 4

Reflects⁵ : {ls : Levels 5} {As : Types _ ls} → Corr _ ℓ As → DProc _ As → Type _
Reflects⁵ = Reflects 5

reflects→decidable
  : {ls : Levels n} {As : Types n ls} {P : Corr n ℓ As} {d : DProc n As}
  → Reflects _ P d → Decidable _ P
reflects→decidable {n = 0}          {d} p   = d because p
reflects→decidable {n = 1}          {d} f x = d x because f x
reflects→decidable {n = suc (suc _)}    f x = reflects→decidable (f x)
