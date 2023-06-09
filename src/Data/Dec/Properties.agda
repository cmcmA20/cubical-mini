{-# OPTIONS --safe #-}
module Data.Dec.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Idiom
open import Meta.Reflection.HLevel

open import Data.Empty.Instances.HLevel
open import Data.Sum.Base

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

open import Data.Dec.Base as Dec
open import Data.Dec.Instances.HLevel

private variable
  ℓ ℓ′ : Level
  P : Type ℓ
  Q : Type ℓ′

infixl 7 _∧ᵈ_
_∧ᵈ_ : Dec P → Dec Q → Dec (P × Q)
(dp ∧ᵈ dq) .does = dp .does and dq .does
(no ¬p ∧ᵈ _    ) .proof = ofⁿ λ p×q → ¬p (p×q .fst)
(yes p ∧ᵈ no ¬q) .proof = ofⁿ λ p×q → ¬q (p×q .snd)
(yes p ∧ᵈ yes q) .proof = ofʸ (p , q)

infixl 6 _∨ᵈ_
_∨ᵈ_ : Dec P → Dec Q → Dec (P ⊎ Q)
(dp ∨ᵈ dq) .does = dp .does or dq .does
(yes p ∨ᵈ _ ) .proof = ofʸ (inl p)
(no ¬p ∨ᵈ no ¬q) .proof = ofⁿ λ where
  (inl p) → ¬p p
  (inr q) → ¬q q
(no ¬p ∨ᵈ yes q) .proof = ofʸ (inr q)

dec-∥-∥₁-equiv : ∥ Dec P ∥₁ ≃ Dec ∥ P ∥₁
dec-∥-∥₁-equiv = prop-extₑ!
  (∥-∥₁.rec! $ Dec.map pure ∥-∥₁.rec!)
  (Dec.rec (yes <$>_) $ pure ∘ no ∘ _∘ pure)
