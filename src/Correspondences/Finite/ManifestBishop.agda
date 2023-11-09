{-# OPTIONS --safe #-}
module Correspondences.Finite.ManifestBishop where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Record
open import Meta.Search.Discrete
open import Meta.Search.HLevel

open import Correspondences.Omniscient

open import Data.Empty.Base
open import Data.Empty.Instances.HLevel
open import Data.Dec.Base as Dec
open import Data.FinSub.Base
open import Data.FinSub.Instances.Discrete
open import Data.Nat
open import Data.Vec.Base
open import Data.Vec.Operations.Computational
open import Data.Vec.Correspondences.Unary.Any.Computational

open import Truncation.Propositional as ∥-∥₁

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

record 𝓑 (A : Type ℓ) : Type ℓ where
  no-eta-equality
  constructor fin
  field
    { cardinality } : ℕ
    enumeration     : A ≃ Fin cardinality

open 𝓑 public

unquoteDecl 𝓑-iso = declare-record-iso 𝓑-iso (quote 𝓑)

𝓑-is-set : is-set (𝓑 A)
𝓑-is-set = is-of-hlevel-≃ _ (iso→equiv 𝓑-iso) hlevel!

𝓑→omniscient₁ : 𝓑 A → Omniscient₁ {ℓ = ℓ′} A
𝓑→omniscient₁ {A} fi .omniscient₁-β {P} P? =
  Dec.map lemma₁ lemma₂ (any? P? xs) where
    n = fi .cardinality
    aeq = fi .enumeration
    module Ã = Equiv aeq
    module Ṽ = Equiv vec-fun-equiv

    xs : Vec A n
    xs = Ṽ.from $ Ã.from

    lemma₁ : Σ[ i ꞉ Fin n ] P (lookup xs i) → ∥ Σ[ a ꞉ A ] P a ∥₁
    lemma₁ = ∣_∣₁ ∘′ bimap (lookup xs) id

    lemma₂ : ¬ Σ[ i ꞉ Fin n ] P (lookup xs i) → ¬ ∥ Σ[ a ꞉ A ] P a ∥₁
    lemma₂ ¬p = ∥-∥₁.rec! $ ¬p ∘ bimap Ã.to (subst P (sym (happly (Ṽ.ε _) _ ∙ Ã.η _)))