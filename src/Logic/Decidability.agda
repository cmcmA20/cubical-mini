{-# OPTIONS --safe #-}
module Logic.Decidability where

open import Meta.Prelude

open import Logic.DoubleNegation

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Dec.Instances.Alternative
open import Data.Dec.Instances.Monoidal
open import Data.Empty.Base as ⊥
open import Data.Reflection.Term
open import Data.Reflects.Path
open import Data.Reflects.Properties
open import Data.Truncation.Propositional.Base as ∥-∥₁
open import Data.Unit.Base

private variable
  ℓ ℓ′ ℓ″ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  n : HLevel

-- Evidence of a correspondence being reflected by a decision procedure

instance
  Decidability-Underlying
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → Decidability A
  Decidability-Underlying ⦃ ua ⦄ .ℓ-decidability = ua .Underlying.ℓ-underlying
  Decidability-Underlying .Decidable X = Dec ⌞ X ⌟
  {-# OVERLAPPABLE Decidability-Underlying #-}

  Reflectance-Underlying
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → Reflectance A Bool
  Reflectance-Underlying ⦃ ua ⦄ .ℓ-reflectance = ua .Underlying.ℓ-underlying
  Reflectance-Underlying .Reflects X = Reflects⁰ ⌞ X ⌟
  {-# OVERLAPPABLE Reflectance-Underlying #-}


dec→essentially-classical : Dec A → Essentially-classical A
dec→essentially-classical = Dec.rec
  (λ a _ → a)
  (λ ¬a f → ⊥.rec $ f ¬a)

instance
  Dec-⊥ : Dec ⊥
  Dec-⊥ = empty
  {-# OVERLAPPING Dec-⊥ #-}

  Dec-⊤ : Dec ⊤
  Dec-⊤ = unit
  {-# OVERLAPPING Dec-⊤ #-}

  Dec-× : ⦃ da : Dec A ⦄ → ⦃ db : Dec B ⦄ → Dec (A × B)
  Dec-× ⦃ da ⦄ ⦃ db ⦄ = da <,> db

  Dec-fun : ⦃ da : Dec A ⦄ → ⦃ db : Dec B ⦄ → Dec (A → B)
  Dec-fun ⦃ da ⦄    ⦃ db ⦄ .does = not (da .does) or db .does
  Dec-fun ⦃ no ¬a ⦄ ⦃ db ⦄ .proof = ofʸ $ λ a → ⊥.rec $ ¬a a
  Dec-fun ⦃ yes a ⦄ ⦃ no ¬b ⦄ .proof = ofⁿ $ ¬b ∘ (_$ a)
  Dec-fun ⦃ yes a ⦄ ⦃ yes b ⦄ .proof = ofʸ λ _ → b
  {-# OVERLAPPABLE Dec-fun #-}

  Dec-¬ : ⦃ da : Dec A ⦄ → Dec (¬ A)
  Dec-¬ ⦃ da ⦄ .does = not (da .does)
  Dec-¬ ⦃ yes a ⦄ .proof = ofⁿ (_$ a)
  Dec-¬ ⦃ no ¬a ⦄ .proof = ofʸ ¬a

  Dec-lift : ⦃ da : Dec A ⦄ → Dec (Lift ℓ A)
  Dec-lift ⦃ da ⦄ .does = da .does
  Dec-lift ⦃ yes a ⦄ .proof = ofʸ (lift a)
  Dec-lift ⦃ no ¬a ⦄ .proof = ofⁿ (¬a ∘ lower)

  Dec-∥-∥₁ : ⦃ da : Dec A ⦄ → Dec ∥ A ∥₁
  Dec-∥-∥₁ ⦃ da ⦄ .does = da .does
  Dec-∥-∥₁ ⦃ yes a ⦄ .proof = ofʸ ∣ a ∣₁
  Dec-∥-∥₁ ⦃ no ¬a ⦄ .proof = ofⁿ $ rec! ¬a
  {-# OVERLAPPABLE Dec-∥-∥₁ #-}

  Dec-universe : Dec (Type ℓ)
  Dec-universe = yes ⊤

  Dec-refl : ∀ {x : A} → Dec (x ＝ x)
  Dec-refl = yes refl
  {-# OVERLAPPING Dec-refl #-}

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
    {ls : Levels arity} (As : Types _ ls)
  → Type (ℓsup arity ls)
DProc arity As = Arrows arity As Bool

DProc⁰ = DProc 0
DProc¹ = DProc 1
DProc² = DProc 2
DProc³ = DProc 3
DProc⁴ = DProc 4
DProc⁵ = DProc 5
