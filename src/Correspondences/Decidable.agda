{-# OPTIONS --safe #-}
module Correspondences.Decidable where

open import Foundations.Base

open import Meta.Reflection
open import Meta.Subst
open import Meta.Variadic

open import Correspondences.Base public
open import Correspondences.Classical

open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.List.Base
open import Data.List.Instances.FromProduct
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
fun-decision (no ¬a) db .proof = ofʸ $ λ a → ⊥.rec (¬a a)
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


-- Decidability of a generalized predicate
Decidableⁿ : Variadic-binding¹
Decidableⁿ {arity} P = Π[ mapⁿ arity Dec ⌞ P ⌟ ]

macro
  Decidable : Term → Term → TC ⊤
  Decidable t hole = do
    ar , r ← variadic-worker t
    und ← variadic-instance-worker r
    unify hole $ def (quote Decidableⁿ)
      [ harg ar , harg unknown , harg unknown
      , harg unknown , harg unknown , iarg und
      , varg t ]


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
Reflectsⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U → DProc _ As → Type (u .ℓ-underlying ⊔ ℓsup _ ls)
Reflectsⁿ {0}                         P d = Reflects⁰ ⌞ P ⌟⁰ d
Reflectsⁿ {1}           {As = A}      P d = Π[ x ꞉ A ] Reflectsⁿ (P x) (d x)
Reflectsⁿ {suc (suc _)} {As = A , As} P d = Π[ x ꞉ A ] Reflectsⁿ (P x) (d x)

macro
  Reflects : Term → Term → Term → TC ⊤
  Reflects c d hole = do
    car , r ← variadic-worker c
    dar , _ ← variadic-worker d
    unify car dar
    und ← variadic-instance-worker r
    unify hole $ def (quote Reflectsⁿ)
      [ harg car , harg unknown , harg unknown
      , harg unknown , harg unknown , iarg und
      , varg c , varg d ]

reflects→decidable
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
    {P : SCorr _ As U} {d : DProc _ As}
  → Reflects P d → Decidable P
reflects→decidable {0}          {d} p   = d because p
reflects→decidable {1}          {d} f x = d x because f x
reflects→decidable {suc (suc _)}    f x = reflects→decidable (f x)
