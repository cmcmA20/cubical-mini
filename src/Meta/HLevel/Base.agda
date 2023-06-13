{-# OPTIONS --safe #-}
module Meta.HLevel.Base where

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
  -- TODO check if `is-contr` definition is good for instance search
  H-Level-is-contr : H-Level (suc n) (is-contr A)
  H-Level-is-contr = prop-instance is-contr-is-prop
