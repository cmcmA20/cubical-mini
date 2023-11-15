{-# OPTIONS --safe #-}
module Meta.Underlying where

open import Foundations.Base

open import Meta.Reflection
open import Meta.Variadic

open import Correspondences.Base public

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Nat.Base

record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟⁰          : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ using (⌞_⌟⁰) public

{-# DISPLAY Underlying.⌞_⌟⁰ f x = ⌞ x ⌟⁰ #-}

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : A → Type ℓ′
  P : Type ℓ′

instance
  Underlying-Σ : ⦃ ua : Underlying A ⦄ → Underlying (Σ A B)
  Underlying-Σ ⦃ ua ⦄ .Underlying.ℓ-underlying = ua .Underlying.ℓ-underlying
  Underlying-Σ .⌞_⌟⁰ x = ⌞ x .fst ⌟⁰

  Underlying-Type : Underlying (Type ℓ)
  Underlying-Type {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟⁰ x = x

  Underlying-Lift : ⦃ ua : Underlying A ⦄ → Underlying (Lift ℓ′ A)
  Underlying-Lift ⦃ ua ⦄ .Underlying.ℓ-underlying = ua .Underlying.ℓ-underlying
  Underlying-Lift .⌞_⌟⁰ x = ⌞ x .lower ⌟⁰


infix 5 _∈_
_∈_ : ⦃ u : Underlying P ⦄ → A → (A → P) → Type _
x ∈ P = ⌞ P x ⌟⁰

infix 5 _∉_
_∉_ : ⦃ u : Underlying P ⦄ → A → (A → P) → Type _
x ∉ P = ¬ x ∈ P

_⊆_ : ⦃ u : Underlying P ⦄ → (A → P) → (A → P) → Type _
U ⊆ V = {x : _} → x ∈ U → x ∈ V


-- correspondence valued in arbitrary structure
SCorr
  : (arity : ℕ) {ls : Levels arity} (As : Types arity ls)
    {ℓ : Level} (P : Type ℓ) ⦃ u : Underlying P ⦄
  → Type (ℓ ⊔ ℓsup arity ls)
SCorr arity As P = Arrows arity As P

Carrierⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {P : Type ℓ} ⦃ u : Underlying P ⦄
  → SCorr arity As P → Corr arity (u .Underlying.ℓ-underlying) As
Carrierⁿ {arity = 0}           C   = ⌞ C ⌟⁰
Carrierⁿ {arity = 1}           C a = ⌞ C a ⌟⁰
Carrierⁿ {arity = suc (suc _)} C a = Carrierⁿ (C a)

carrier-macro : Term → Term → TC ⊤
carrier-macro t hole = withReduceDefs (false , [ quote Arrows ]) do
  ty ← inferType t >>= reduce
  debugPrint "tactic.variadic" 20 [ "Type hint: " , termErr ty ]
  let ar , sig , lv , r = get-arity-sig-lvl-type ty
  solved@(meta mv _) ← new-meta (def (quote Underlying) [ harg unknown , varg r ])
    where _ → typeError [ "Could not get `Underlying` instances: " , termErr r ]
  (und ∷ []) ← getInstances mv where
    [] → typeError [ "No `Underlying `instances for ", termErr r ]
    _  → typeError [ "Multiple `Underlying` instances for ", termErr r ]
  unify solved und
  let
    solution = def (quote Carrierⁿ)
      [ harg ar , harg unknown , harg sig
      , harg lv , harg r , iarg und
      , varg t ]
  debugPrint "tactic.variadic" 20
    [ "Candidate solution: " , termErr solution , "\n"
    , "Arity: " , termErr ar , "\n"
    , "Signature: " , termErr sig , "\n"
    , "Level: " , termErr lv , "\n" ]
  unify hole solution

macro ⌞_⌟ = carrier-macro
