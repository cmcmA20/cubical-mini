{-# OPTIONS --safe #-}
module Meta.Discrete where

open import Foundations.Base

open import Meta.HLevel

open import Correspondences.Nullary.Discrete public

open import Data.Dec.Base public
  using (Dec; yes; no)
open import Data.Dec.Base as Dec

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  n : HLevel

record Discrete {ℓ} (T : Type ℓ) : Type ℓ where
  constructor discrete-instance
  field
    _≟_ : is-discrete T

open Discrete ⦃ ... ⦄ public

discrete : ⦃ d : Discrete A ⦄ → is-discrete A
discrete ⦃ d ⦄ = d ._≟_

Discrete-is-prop : is-prop (Discrete A)
Discrete-is-prop d₁ d₂ i ._≟_ =
  is-discrete-is-prop (d₁ ._≟_) (d₂ ._≟_) i

-- sadly it has to be here for now
-- TODO check how this interacts with the usual machinery
-- maybe we need a unified solver for discreteness and h-levels?
-- it should be easy as both are properties of types
instance
  H-Level-Discrete : ⦃ Discrete A ⦄ → H-Level (2 + n) A
  H-Level-Discrete =
    basic-instance 2 (is-discrete→is-set _≟_)

  H-Level-Discrete′ : ⦃ Discrete A ⦄ → H-Level (suc n) (Discrete A)
  H-Level-Discrete′ = prop-instance Discrete-is-prop

instance
  Discrete-H-Level : Discrete (H-Level n A)
  Discrete-H-Level ._≟_ (hlevel-instance _) (hlevel-instance _) =
    yes (ap hlevel-instance (is-of-hlevel-is-prop _ _ _))

  Discrete-Σ
    : {A : Type ℓ} {B : A → Type ℓ′}
    → ⦃ Discrete A ⦄ → ⦃ ∀ {a} → Discrete (B a) ⦄
    → Discrete (Σ A B)
  Discrete-Σ {B} ._≟_ (a₁ , b₁) (a₂ , b₂) with a₁ ≟ a₂
  ... | no ¬p = no λ q → ¬p (ap fst q)
  ... | yes p with subst _ p b₁ ≟ b₂
  ... | no ¬q = no λ r → ¬q $ from-pathP $
    subst (λ X → ＜ b₁ ／ (λ i → B (X i)) ＼ b₂ ＞)
          (is-discrete→is-set discrete a₁ a₂ (ap fst r) p)
          (ap snd r)
  ... | yes q = yes (Σ-path p q)

  Discrete-Lift
    : ⦃ Discrete A ⦄ → Discrete (Lift ℓ A)
  Discrete-Lift .Discrete._≟_ (lift x) (lift y) =
    Dec.map (ap lift) (_∘ ap lower) (x ≟ y)

  Discrete-path
    : ⦃ Discrete A ⦄ → {x y : A} → Discrete (x ＝ y)
  Discrete-path .Discrete._≟_ _ _ =
    yes (is-discrete→is-set discrete _ _ _ _)
