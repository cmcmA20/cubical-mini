{-# OPTIONS --safe #-}
module Data.Empty.Base where

open import Foundations.Base
open import Foundations.HLevel.Base

data ⊥ₜ : Type where

instance
  ⊥-Type-small : ⊥-notation Type
  ⊥-Type-small .⊥ = ⊥ₜ
  {-# OVERLAPPING ⊥-Type-small #-}

  ⊥-Type : ∀ {ℓ} → ⊥-notation (Type ℓ)
  ⊥-Type .⊥ = Lift _ ⊥ₜ
  {-# INCOHERENT ⊥-Type #-}

private variable
  ℓ ℓ′ ℓ″ : Level
  @0 A : Type ℓ
  @0 x y : ⊥ₜ
  @0 Aω : Typeω
  n : HLevel

rec : @0 ⊥ → A
rec ()

rec′ : @irr ⊥ → A
rec′ ()

absurd = rec

elim : {@0 A : ⊥ → Type ℓ} → (@0 x : ⊥) → A x
elim ()

⊥-ext : x ＝ y
⊥-ext {x = ()}

absurd-path : {@0 y : A} {@0 x : ⊥} → absurd x ＝ y
absurd-path {x = ()}

infixr 0 ¬ₜ_
¬ₜ_ : Type ℓ → Type ℓ
¬ₜ A = A ⇒ ⊥

instance
  ¬-Type : ¬-notation (𝒰 ℓ) (𝒰 ℓ)
  ¬-Type .¬_ = ¬ₜ_

infix 4 _≠_
_≠_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≠ y = ¬ x ＝ y

contra
  : ∀{ℓ ℓ′} {@0 A : Type ℓ} {@0 B : Type ℓ′}
  → (  A →   B)
  → (¬ B → ¬ A)
contra f ¬b a = ¬b (f a)

opaque
  ⊥-is-prop : is-prop ⊥
  ⊥-is-prop ()

  ¬-is-prop : is-prop (¬ A)
  ¬-is-prop ¬a₁ ¬a₂ i a = ⊥-ext {x = ¬a₁ a} {y = ¬a₂ a} i

instance opaque
  H-Level-⊥ : H-Level (suc n) ⊥
  H-Level-⊥ = hlevel-prop-instance ⊥-is-prop
  {-# OVERLAPPING H-Level-⊥ #-}

  H-Level-¬ : {A : Type ℓ} → H-Level (suc n) (¬ A)
  H-Level-¬ = hlevel-prop-instance ¬-is-prop
  {-# OVERLAPPING H-Level-¬ #-}


data ⊥ω : Typeω where

⊥→⊥ω : ⊥ → ⊥ω
⊥→⊥ω ()

recω : @0 ⊥ω → A
recω ()

recω-irr : @irr ⊥ω → A
recω-irr ()

elimω : {@0 A : ⊥ω → Typeω} → (@0 x : ⊥ω) → A x
elimω ()

infix 30 _∉_ _∉!_
_∉_ _∉!_ : {A : Type ℓ} {ℙA : Type ℓ′} ⦃ m : Membership A ℙA ℓ″ ⦄
         → A → ℙA → Type ℓ″
x ∉  y = ¬ x ∈ y
x ∉! y = ¬ x ∈! y
