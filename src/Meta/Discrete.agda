{-# OPTIONS --safe #-}
module Meta.Discrete where

open import Foundations.Base

open import Meta.HLevel

open import Structures.Discrete

private variable
  ℓ : Level
  A : Type ℓ

record Discrete {ℓ} (T : Type ℓ) : Type ℓ where
  constructor discrete-instance
  field
    has-discrete : is-discrete T

open Discrete

discrete : ⦃ d : Discrete A ⦄ → is-discrete A
discrete ⦃ d ⦄ = d .has-discrete

Discrete-is-prop : is-prop (Discrete A)
Discrete-is-prop d₁ d₂ i .has-discrete =
  is-discrete-is-prop (d₁ .has-discrete) (d₂ .has-discrete) i

-- sadly it has to be here for now
-- TODO check how this interacts with the usual machinery
-- maybe we need a unified solver for discreteness and h-levels?
-- it should be easy as both are properties of types
instance
  H-Level-Discrete : {n : HLevel} ⦃ d : Discrete A ⦄ → H-Level (2 + n) A
  H-Level-Discrete ⦃ d ⦄ =
    basic-instance 2 (is-discrete→is-set (d .has-discrete))

-- TODO all the generic instances

-- instance
--   H-Level-Π
--     : {B : A → Type ℓ}
--     → ⦃ ∀ {a} → H-Level n (B a) ⦄
--     → H-Level n (Π[ x ꞉ A ] B x)
--   H-Level-Π {n} .has-hlevel = Π-is-of-hlevel n λ _ → hlevel n

--   H-Level-Π-implicit
--     : {B : A → Type ℓ}
--     → ⦃ ∀ {a} → H-Level n (B a) ⦄
--     → H-Level n (∀ {a} → B a)
--   H-Level-Π-implicit {n} .has-hlevel = Π-is-of-hlevel-implicit n λ _ → hlevel n

--   H-Level-Σ
--     : {B : A → Type ℓ}
--     → ⦃ H-Level n A ⦄ → ⦃ ∀ {a} → H-Level n (B a) ⦄
--     → H-Level n (Σ A B)
--   H-Level-Σ {n} .has-hlevel =
--     Σ-is-of-hlevel n (hlevel n) λ _ → hlevel n

--   H-Level-path′
--     : ⦃ s : H-Level (suc n) A ⦄ {x y : A} → H-Level n (x ＝ y)
--   H-Level-path′ {n} .has-hlevel = Path-is-of-hlevel′ n (hlevel (suc n)) _ _

--   H-Level-Lift
--     : ⦃ s : H-Level n A ⦄ → H-Level n (Lift ℓ A)
--   H-Level-Lift {n} .has-hlevel = Lift-is-of-hlevel n (hlevel n)
