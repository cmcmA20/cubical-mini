{-# OPTIONS --safe #-}
module Data.Dec.Instances.Extensional where

open import Foundations.Base

open import Meta.Extensionality
open import Meta.Search.HLevel

open import Data.Empty.Base
open import Data.Dec.Base
open import Data.Unit.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

Extensional-Dec : ⦃ sa : Extensional A ℓ′ ⦄ → Extensional (Dec A) ℓ′
Extensional-Dec ⦃ sa ⦄ .Pathᵉ (_ because ofʸ p) (_ because ofʸ q) = Pathᵉ sa p q
Extensional-Dec        .Pathᵉ (_ because ofⁿ _) (_ because ofⁿ _) = Lift _ ⊤
Extensional-Dec        .Pathᵉ _                 _                 = Lift _ ⊥
Extensional-Dec ⦃ sa ⦄ .reflᵉ (_ because ofʸ p) = reflᵉ sa p
Extensional-Dec        .reflᵉ (_ because ofⁿ _) = _
Extensional-Dec ⦃ sa ⦄ .idsᵉ .to-path {a = _ because ofʸ a} {b = _ because ofʸ b} =
  ap yes ∘ sa .idsᵉ .to-path
Extensional-Dec        .idsᵉ .to-path {a = _ because ofⁿ a} {b = _ because ofⁿ _} _ =
  ap no prop!
Extensional-Dec ⦃ sa ⦄ .idsᵉ .to-path-over {_ because ofʸ _} {_ because ofʸ _} =
  sa .idsᵉ .to-path-over
Extensional-Dec        .idsᵉ .to-path-over {_ because ofⁿ _} {_ because ofⁿ _} _ = refl

instance
  extensionality-dec : Extensionality (Dec A)
  extensionality-dec .Extensionality.lemma = quote Extensional-Dec
