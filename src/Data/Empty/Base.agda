{-# OPTIONS --safe #-}
module Data.Empty.Base where

open import Foundations.Base
open import Foundations.HLevel.Base

data ⊥ : Type where

private variable
  ℓ ℓ′ : Level
  @0 A : Type ℓ
  @0 x y : ⊥
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

infixr 0 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

infix 4 _≠_
_≠_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≠ y = ¬ x ＝ y

contra
  : ∀{ℓ ℓ′} {@0 A : Type ℓ} {@0 B : Type ℓ′}
  → (  A →   B)
  → (¬ B → ¬ A)
contra f ¬b a = ¬b (f a)

opaque
  unfolding is-of-hlevel

  ⊥-is-prop : is-prop ⊥
  ⊥-is-prop ()

  ¬-is-prop : is-prop (¬ A)
  ¬-is-prop ¬a₁ ¬a₂ i a = ⊥-ext {x = ¬a₁ a} {y = ¬a₂ a} i

instance
  H-Level-⊥ : H-Level (suc n) ⊥
  H-Level-⊥ = hlevel-prop-instance ⊥-is-prop

  H-Level-¬ : {A : Type ℓ} → H-Level (suc n) (¬ A)
  H-Level-¬ = hlevel-prop-instance ¬-is-prop

⊥-is-of-hlevel : ∀ n → is-of-hlevel (suc n) ⊥
⊥-is-of-hlevel _ = hlevel _

¬-is-of-hlevel : {A : Type ℓ} → ∀ n → is-of-hlevel (suc n) (¬ A)
¬-is-of-hlevel _ = hlevel _


data ⊥ω : Typeω where

⊥→⊥ω : ⊥ → ⊥ω
⊥→⊥ω ()

recω : @0 ⊥ω → A
recω ()

recω-irr : @irr ⊥ω → A
recω-irr ()

elimω : {@0 A : ⊥ω → Typeω} → (@0 x : ⊥ω) → A x
elimω ()
