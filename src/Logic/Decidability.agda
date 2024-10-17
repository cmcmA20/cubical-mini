{-# OPTIONS --safe #-}
module Logic.Decidability where

open import Meta.Prelude

open import Logic.DoubleNegation

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Dec.Instances.Alternative
open import Data.Dec.Instances.Monoidal
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base
open import Data.Truncation.Propositional.Base as ∥-∥₁
open import Data.Unit.Base

private variable
  ℓ ℓ′ ℓ″ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  n : HLevel

dec→essentially-classical : Dec A → Essentially-classical A
dec→essentially-classical = Dec.rec
  (λ a _ → a)
  (λ ¬a f → false! $ f ¬a)

instance
  Dec-⊥ : Dec ⊥
  Dec-⊥ = empty
  {-# OVERLAPPING Dec-⊥ #-}

  Dec-⊤ : Dec ⊤
  Dec-⊤ = unit
  {-# OVERLAPPING Dec-⊤ #-}

  Dec-× : ⦃ da : Dec A ⦄ → ⦃ db : Dec B ⦄ → Dec (A × B)
  Dec-× ⦃ da ⦄ ⦃ db ⦄ .does = ⌊ da ⌋ and ⌊ db ⌋
  Dec-× ⦃ da ⦄ ⦃ db ⦄ .proof = Reflects-× ⦃ da .proof ⦄ ⦃ db .proof ⦄

  Dec-fun : ⦃ da : Dec A ⦄ → ⦃ db : Dec B ⦄ → Dec (A → B)
  Dec-fun ⦃ da ⦄ ⦃ db ⦄ .does = ⌊ da ⌋ implies ⌊ db ⌋
  Dec-fun ⦃ da ⦄ ⦃ db ⦄ .proof = Reflects-⇒ ⦃ da .proof ⦄ ⦃ db .proof ⦄
  {-# OVERLAPPABLE Dec-fun #-}

  Dec-¬ : ⦃ da : Dec A ⦄ → Dec (¬ A)
  Dec-¬ ⦃ da ⦄ .does = not ⌊ da ⌋
  Dec-¬ ⦃ da ⦄ .proof = Reflects-¬ ⦃ da .proof ⦄

  Dec-lift : ⦃ da : Dec A ⦄ → Dec (Lift ℓ A)
  Dec-lift ⦃ da ⦄ .does = da .does
  Dec-lift ⦃ da ⦄ .proof = Reflects-Lift ⦃ da .proof ⦄

  Dec-∥-∥₁ : ⦃ da : Dec A ⦄ → Dec ∥ A ∥₁
  Dec-∥-∥₁ ⦃ da ⦄ .does = ⌊ da ⌋
  Dec-∥-∥₁ ⦃ da ⦄ .proof = Reflects-∥-∥₁ ⦃ da .proof ⦄
  {-# OVERLAPPABLE Dec-∥-∥₁ #-}

  Dec-universe : Dec (Type ℓ)
  Dec-universe = yes ⊤

Dec-prop-Σ
  : {A : Type ℓᵃ} {B : A → Type ℓᵇ}
  → is-prop A
  → Dec A
  → Decidable B
  → Dec (Σ[ a ꞉ A ] B a)
Dec-prop-Σ A-pr (no ¬a) _  = no (¬a ∘ fst)
Dec-prop-Σ {B} A-pr (yes a) db with db {a}
... | no ¬b = no (λ x → ¬b (subst B (A-pr (x .fst) a) (x .snd)))
... | yes b = yes (a , b)


-- Decision procedure
DProc
  : (arity : ℕ)
    {ls : Levels arity} (As : TyVec _ ls)
  → Type (ℓsup arity ls)
DProc arity As = Arrows arity As Bool

DProc⁰ = DProc 0
DProc¹ = DProc 1
DProc² = DProc 2
DProc³ = DProc 3
DProc⁴ = DProc 4
DProc⁵ = DProc 5
