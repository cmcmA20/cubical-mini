{-# OPTIONS --safe #-}
module Meta.Decision.Base where

open import Foundations.Base

open import Meta.HLevel

open import Correspondences.Nullary.Decidable public

import Data.Dec.Base as Dec
open Dec using (Dec; yes; no)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  n : HLevel

record Decision {ℓ} (n : HLevel) (T : Type ℓ) : Type ℓ where
  constructor decision-instance
  field
    has-decidable : is-decidable-at-hlevel n T

open Decision ⦃ ... ⦄ public

Discrete : Type ℓ → Type ℓ
Discrete = Decision 1

decide : (n : HLevel) ⦃ d : Decision n A ⦄ → is-decidable-at-hlevel n A
decide n ⦃ d ⦄ = d .has-decidable

_≟_ : ⦃ Discrete A ⦄ → (x y : A) → Dec (x ＝ y)
_≟_ = decide 1

opaque
  unfolding is-of-hlevel
  Decision-is-prop : is-prop (Decision (suc n) A)
  Decision-is-prop {n} d₁ d₂ i .has-decidable =
    is-decidable-at-hlevel-is-prop n (d₁ .has-decidable) (d₂ .has-decidable) i

instance opaque
  unfolding is-of-hlevel
  discrete-is-of-hlevel : ⦃ Discrete A ⦄ → is-of-hlevel (2 + n) A
  discrete-is-of-hlevel = is-of-hlevel-+-left 2 _ (is-discrete→is-set _≟_)

  HLevel-Discrete′ : is-of-hlevel (suc n) (Discrete A)
  HLevel-Discrete′ = is-prop→is-of-hlevel-suc Decision-is-prop

-- TODO check if it's useful
-- instance
--   Discrete-H-Level : Discrete (is-of-hlevel n A)
--   Discrete-H-Level .has-decidable (hlevel-instance _) (hlevel-instance _) =
--     yes (ap hlevel-instance (is-of-hlevel-is-prop _ _ _))

-- TODO remove
  Discrete-Σ
    : {A : Type ℓ} {B : A → Type ℓ′}
    → ⦃ Discrete A ⦄ → ⦃ ∀ {a} → Discrete (B a) ⦄
    → Discrete (Σ A B)
  Discrete-Σ {B} .has-decidable (a₁ , b₁) (a₂ , b₂) with a₁ ≟ a₂
  ... | no ¬p = no λ q → ¬p (ap fst q)
  ... | yes p with subst _ p b₁ ≟ b₂
  ... | no ¬q = no λ r → ¬q $ from-pathP $
    subst (λ X → ＜ b₁ ／ (λ i → B (X i)) ＼ b₂ ＞)
          (is-discrete→is-set _≟_ a₁ a₂ (ap fst r) p)
          (ap snd r)
  ... | yes q = yes (Σ-path p q)

  Discrete-Lift
    : ⦃ Discrete A ⦄ → Discrete (Lift ℓ A)
  Discrete-Lift .has-decidable (lift x) (lift y) =
    Dec.map (ap lift) (_∘ ap lower) (x ≟ y)

  Discrete-path
    : ⦃ Discrete A ⦄ → {x y : A} → Discrete (x ＝ y)
  Discrete-path .has-decidable _ _ =
    yes (is-discrete→is-set _≟_ _ _ _ _)
