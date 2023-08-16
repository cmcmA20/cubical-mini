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


Decidable : Pred _ (Corr n ℓ A)
Decidable P = Π[ Dec ∘ⁿ P ]


DProc
  : (arity : ℕ) (ℓ′ : Level)
    {ℓ : Level} (A : Type ℓ)
  → Type (Levelₓ ℓ 0ℓ arity)
DProc arity ℓ′ A = functionₓ arity A Bool

DProc⁰ = DProc 0
DProc¹ = DProc 1
DProc² = DProc 2
DProc³ = DProc 3

Reflects : Corr n ℓ A → DProc n ℓ A → Type (level-of-type A ⊔ ℓ)
Reflects {n = 0}     {A} P f = Lift (level-of-type A) (Reflects¹ P f)
Reflects {n = suc n} {A} P f = Π[ (λ (x : A) → Reflects (P x) (f x)) ]

reflects→decidable : {A : Type ℓᵃ} {P : Corr n ℓ A} {Q : DProc n ℓ A} → Reflects P Q → Decidable P
reflects→decidable {n = 0} (lift p) = lift (_ because p)
reflects→decidable {n = 1} {Q} f x = Q x because lower (f x)
reflects→decidable {n = suc (suc _)} f x = reflects→decidable (f x)

-- witness→decision : {A : Type ℓᵃ} {P : Corr n ℓ A} {Q : DProc n ℓ A} → Reflects P Q → Π[ P ⇒ ((_＝ true) ∘ⁿ Q) ]
-- witness→decision {n = 0} (lift (ofʸ p))  = lift λ _ → refl
-- witness→decision {n = 0} (lift (ofⁿ ¬p)) = lift λ p → absurd (¬p p)
-- witness→decision {n = 1} {A} f x = lower $ witness→decision {n = 0} {A = A} $ f x
-- witness→decision {n = suc (suc _)} f x = witness→decision (f x)

-- decision→witness : {A : Type ℓᵃ} {P : Corr n ℓ A} {Q : DProc n ℓ A} → Reflects P Q → Π[ ((_＝ true) ∘ⁿ Q) ⇒ P ]
-- decision→witness {n = 0} (lift (ofʸ p)) = lift λ _ → p
-- decision→witness {n = 0} (lift (ofⁿ ¬p)) = lift λ p → absurd (false≠true p)
-- decision→witness {n = 1} {A} f x = lower $ decision→witness {A = A} $ f x
-- decision→witness {n = suc (suc _)} f x = decision→witness (f x)
