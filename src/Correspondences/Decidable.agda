{-# OPTIONS --safe #-}
module Correspondences.Decidable where

open import Foundations.Base

open import Correspondences.Base public
open import Correspondences.Classical

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
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


Decidable : Pred _ (Corr n ℓ′ A)
Decidable P = Π[ Dec ∘ⁿ P ]
