{-# OPTIONS --safe #-}
module Data.Nat.Properties where

open import Meta.Prelude

open import Correspondences.Decidable

open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Nat.Base public
open import Data.Nat.Path

private variable n : ℕ

-- addition

+-zero-r : (x : ℕ) → x + 0 ＝ x
+-zero-r 0       = refl
+-zero-r (suc x) = ap suc (+-zero-r x)

+-suc-r : (x y : ℕ) → x + suc y ＝ suc (x + y)
+-suc-r 0       y = refl
+-suc-r (suc x) y = ap suc (+-suc-r x y)

+-comm : (x y : ℕ) → x + y ＝ y + x
+-comm 0       y = sym (+-zero-r y)
+-comm (suc x) y = ap suc (+-comm x y) ∙ sym (+-suc-r y x)

+-assoc : (x y z : ℕ) → x + (y + z) ＝ x + y + z
+-assoc 0       _ _ = refl
+-assoc (suc x) y z = ap suc (+-assoc x _ _)

+-inj-l : (x y z : ℕ) → x + y ＝ x + z → y ＝ z
+-inj-l 0       y z p = p
+-inj-l (suc x) y z p = +-inj-l _ _ _ (suc-inj p)

+-inj-r : (x y z : ℕ) → x + z ＝ y + z → x ＝ y
+-inj-r x y z p = +-inj-l _ _ _ (+-comm z x ∙ p ∙ +-comm y z)

+-comm-assoc : (x y z : ℕ) → x + (y + z) ＝ y + (x + z)
+-comm-assoc x y z = +-assoc x y _
                   ∙ ap (_+ z) (+-comm x y)
                   ∙ sym (+-assoc y x _)

+-assoc-comm : (x y z : ℕ) → x + y + z ＝ x + z + y
+-assoc-comm x y z = sym (+-assoc x _ _) ∙ ap (x +_) (+-comm y z) ∙ +-assoc x _ _


-- multiplication

·-absorb-r : (x : ℕ) → x · zero ＝ zero
·-absorb-r 0       = refl
·-absorb-r (suc x) = ·-absorb-r x

·-zero : (x y : ℕ) → x · y ＝ 0 → (x ＝ 0) ⊎ (y ＝ 0)
·-zero 0       _       _ = inl refl
·-zero (suc _) 0       _ = inr refl
·-zero (suc _) (suc _) p = absurd (suc≠zero p)

·-suc-r : (x y : ℕ) → x · suc y ＝ x + x · y
·-suc-r 0       _ = refl
·-suc-r (suc x) y = ap suc $ ap (y +_) (·-suc-r x y) ∙ +-comm-assoc y x _

·-comm : (x y : ℕ) → x · y ＝ y · x
·-comm 0       y = sym (·-absorb-r y)
·-comm (suc x) y = ap (y +_) (·-comm x _) ∙ sym (·-suc-r y x)

·-id-l : (x : ℕ) → 1 · x ＝ x
·-id-l = +-zero-r

·-id-r : (x : ℕ) → x · 1 ＝ x
·-id-r x = ·-comm x 1 ∙ ·-id-l x

·-distrib-+-r : (x y z : ℕ) → (x + y) · z ＝ x · z + y · z
·-distrib-+-r 0       _ _ = refl
·-distrib-+-r (suc x) y z = ap (z +_) (·-distrib-+-r x y z) ∙ +-assoc z (x · z) (y · z)

·-distrib-+-l : (x y z : ℕ) → x · (y + z) ＝ x · y + x · z
·-distrib-+-l x y z = ·-comm x (y + z) ∙ ·-distrib-+-r y z x ∙ ap² (_+_) (·-comm y x) (·-comm z x)

·-assoc : (x y z : ℕ) → x · (y · z) ＝ x · y · z
·-assoc 0       _ _ = refl
·-assoc (suc x) y z = ap (y · z +_) (·-assoc x y z) ∙ sym (·-distrib-+-r y _ _)


-- minimum

min-absorb-l : (x : ℕ) → min 0 x ＝ 0
min-absorb-l 0       = refl
min-absorb-l (suc _) = refl

min-absorb-r : (x : ℕ) → min x 0 ＝ 0
min-absorb-r 0       = refl
min-absorb-r (suc _) = refl

min-comm : (x y : ℕ) → min x y ＝ min y x
min-comm 0       y       = min-absorb-l y ∙ sym (min-absorb-r y)
min-comm (suc _) 0       = refl
min-comm (suc x) (suc y) = ap suc $ min-comm x y

min-assoc : (x y z : ℕ) → min x (min y z) ＝ min (min x y) z
min-assoc 0       y       z       = min-absorb-l (min y z) ∙ sym (min-absorb-l z) ∙ ap (λ q → min q z) (min-absorb-l y ⁻¹)
min-assoc (suc x) 0       z       = ap (min (suc x)) (min-absorb-l z) ∙ sym (min-absorb-l z)
min-assoc (suc _) (suc _) 0       = refl
min-assoc (suc x) (suc y) (suc z) = ap suc $ min-assoc x y z

min-idem : (x : ℕ) → min x x ＝ x
min-idem 0       = refl
min-idem (suc x) = ap suc $ min-idem x

-- maximum

max-id-l : (x : ℕ) → max 0 x ＝ x
max-id-l 0       = refl
max-id-l (suc _) = refl

max-id-r : (x : ℕ) → max x 0 ＝ x
max-id-r 0       = refl
max-id-r (suc _) = refl

max-comm : (x y : ℕ) → max x y ＝ max y x
max-comm 0       y       = max-id-l y ∙ sym (max-id-r y)
max-comm (suc _) 0       = refl
max-comm (suc x) (suc y) = ap suc $ max-comm x y

max-assoc : (x y z : ℕ) → max x (max y z) ＝ max (max x y) z
max-assoc 0       y       z       = max-id-l (max y z) ∙ ap (λ q → max q z) (max-id-l y ⁻¹)
max-assoc (suc x) 0       z       = ap (max (suc x)) (max-id-l z)
max-assoc (suc x) (suc y) 0       = refl
max-assoc (suc x) (suc y) (suc z) = ap suc $ max-assoc x y z

max-idem : (x : ℕ) → max x x ＝ x
max-idem 0       = refl
max-idem (suc x) = ap suc $ max-idem x

-- iteration

iter-add : {ℓ : Level} {A : 𝒰 ℓ}
         → (m n : ℕ) → (f : A → A) → (x : A)
         → iter (m + n) f x ＝ iter m f (iter n f x)
iter-add  zero   n f x = refl
iter-add (suc m) n f x = ap f (iter-add m n f x)

iter-mul : {ℓ : Level} {A : 𝒰 ℓ}
         → (m n : ℕ) → (f : A → A) → (x : A)
         → iter (m · n) f x ＝ iter m (iter n f) x
iter-mul  zero   n f x = refl
iter-mul (suc m) n f x = iter-add n (m · n) f x ∙ ap (iter n f) (iter-mul m n f x)


instance
  is-zero-decision : Decidable (is-zero n)
  is-zero-decision {0}     = yes tt
  is-zero-decision {suc _} = no  refl

  is-positive-decision : Decidable (is-positive n)
  is-positive-decision {0}     = no  refl
  is-positive-decision {suc _} = yes tt
