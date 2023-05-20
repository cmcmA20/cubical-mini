{-# OPTIONS --safe #-}
module Meta.HLevel where

open import Foundations.Base
open import Foundations.HLevel public

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

record H-Level {ℓ} (n : HLevel) (T : Type ℓ) : Type ℓ where
  constructor hlevel-instance
  field
    has-hlevel : is-of-hlevel n T

open H-Level

hlevel : (n : HLevel) ⦃ x : H-Level n A ⦄ → is-of-hlevel n A
hlevel n ⦃ x ⦄ = x .has-hlevel

H-Level-is-prop : is-prop (H-Level n A)
H-Level-is-prop {n} x y i .has-hlevel =
  is-of-hlevel-is-prop n (x .has-hlevel) (y .has-hlevel) i

basic-instance : (n : HLevel) → is-of-hlevel n A → ∀ {k} → H-Level (n + k) A
basic-instance {A} n hl {k} =
  subst (λ h → H-Level h A) (+-comm n k) (hlevel-instance (is-of-hlevel-+ n k hl))
  where
    +-comm : ∀ n k → k + n ＝ n + k
    +-comm zero k = go k where
      go : ∀ k → k + 0 ＝ k
      go zero = refl
      go (suc x) = ap suc (go x)
    +-comm (suc n) k = go n k ∙ ap suc (+-comm n k) where
      go : ∀ n k → k + suc n ＝ suc (k + n)
      go n zero = refl
      go n (suc k) = ap suc (go n k)

prop-instance : is-prop A → ∀ {k} → H-Level (suc k) A
prop-instance {A} hl = hlevel-instance (is-prop→is-hlevel-suc hl)


instance
  H-Level-Π
    : {B : A → Type ℓ}
    → ⦃ ∀ {a} → H-Level n (B a) ⦄
    → H-Level n (Π[ x ꞉ A ] B x)
  H-Level-Π {n} .has-hlevel = Π-is-of-hlevel n λ _ → hlevel n

  H-Level-Π-implicit
    : {B : A → Type ℓ}
    → ⦃ ∀ {a} → H-Level n (B a) ⦄
    → H-Level n (∀ {a} → B a)
  H-Level-Π-implicit {n} .has-hlevel = Π-is-of-hlevel-implicit n λ _ → hlevel n

  H-Level-Σ
    : {B : A → Type ℓ}
    → ⦃ H-Level n A ⦄ → ⦃ ∀ {a} → H-Level n (B a) ⦄
    → H-Level n (Σ A B)
  H-Level-Σ {n} .has-hlevel =
    Σ-is-of-hlevel n (hlevel n) λ _ → hlevel n

  H-Level-path′
    : ⦃ s : H-Level (suc n) A ⦄ {x y : A} → H-Level n (x ＝ y)
  H-Level-path′ {n} .has-hlevel = Path-is-of-hlevel′ n (hlevel (suc n)) _ _

  H-Level-Lift
    : ⦃ s : H-Level n A ⦄ → H-Level n (Lift ℓ A)
  H-Level-Lift {n} .has-hlevel = Lift-is-of-hlevel n (hlevel n)

  -- TODO check if `is-contr` definition is good for instance search
  H-Level-is-contr : H-Level (suc n) (is-contr A)
  H-Level-is-contr = prop-instance is-contr-is-prop
