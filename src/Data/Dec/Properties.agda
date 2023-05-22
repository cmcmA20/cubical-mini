{-# OPTIONS --safe #-}
module Data.Dec.Properties where

open import Foundations.Base

open import Data.Sum.Base

open import Data.Dec.Base

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
(yes p ∨ᵈ _ ) .proof = ofʸ (inj-l p)
(no ¬p ∨ᵈ no ¬q) .proof = ofⁿ λ where
  (inj-l p) → ¬p p
  (inj-r q) → ¬q q
(no ¬p ∨ᵈ yes q) .proof = ofʸ (inj-r q)

¬ᵈ_ : Dec P → Dec (¬ P)
¬ᵈ_ x .does = not (x .does)
¬ᵈ_ (yes p) .proof = ofⁿ (λ ¬p → ¬p p)
¬ᵈ_ (no ¬p) .proof = ofʸ ¬p
