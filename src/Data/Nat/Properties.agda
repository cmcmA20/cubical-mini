{-# OPTIONS --safe #-}
module Data.Nat.Properties where

open import Foundations.Prelude

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Nat.Base public
open import Data.Nat.Path
open import Data.Reflects.Base as R

private variable
  m n : ℕ

s=s≃ : (m ＝ n) ≃ (suc m ＝ suc n)
s=s≃ = prop-extₑ! (ap suc) suc-inj

-- addition

+-zero-r : (x : ℕ) → x + 0 ＝ x
+-zero-r 0       = refl
+-zero-r (suc x) = ap suc (+-zero-r x)

+-suc-r : (x y : ℕ) → x + suc y ＝ suc (x + y)
+-suc-r 0       y = refl
+-suc-r (suc x) y = ap suc (+-suc-r x y)

+-comm : (x y : ℕ) → x + y ＝ y + x
+-comm 0       y = (+-zero-r y) ⁻¹
+-comm (suc x) y = ap suc (+-comm x y) ∙ (+-suc-r y x) ⁻¹

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
                   ∙ (+-assoc y x _) ⁻¹

+-assoc-comm : (x y z : ℕ) → x + y + z ＝ x + z + y
+-assoc-comm x y z = (+-assoc x _ _) ⁻¹ ∙ ap (x +_) (+-comm y z) ∙ +-assoc x _ _

+-interchange : (x y z w : ℕ) → (x + y) + (z + w) ＝ (x + z) + (y + w)
+-interchange x y z w = (+-assoc x y (z + w)) ⁻¹ ∙ ap (x +_) (+-comm-assoc y z w) ∙ +-assoc x z (y + w)

+-cancel-l : ∀ m n1 n2 → m + n1 ＝ m + n2 → n1 ＝ n2
+-cancel-l  zero   n1 n2 e = e
+-cancel-l (suc m) n1 n2 e = +-cancel-l m n1 n2 (suc-inj e)

+-cancel-r : ∀ m1 m2 n → m1 + n ＝ m2 + n → m1 ＝ m2
+-cancel-r m1 m2 n e = +-cancel-l n m1 m2 (+-comm n m1 ∙ e ∙ +-comm m2 n)

+=0-2 : ∀ m n → m + n ＝ 0 → (m ＝ 0) × (n ＝ 0)
+=0-2  zero    zero   e = refl , refl
+=0-2  zero   (suc n) e = false! e
+=0-2 (suc m)  n      e = false! e


-- subtraction

pred=∸1 : ∀ n → pred n ＝ n ∸ 1
pred=∸1  zero   = refl
pred=∸1 (suc n) = refl

∸-cancel : ∀ n → n ∸ n ＝ 0
∸-cancel  zero   = refl
∸-cancel (suc n) = ∸-cancel n

∸-zero-l : ∀ n → 0 ∸ n ＝ 0
∸-zero-l  zero   = refl
∸-zero-l (suc n) = refl

∸-cancel-+-l : ∀ p m n → (p + m) ∸ (p + n) ＝ m ∸ n
∸-cancel-+-l  zero   m n = refl
∸-cancel-+-l (suc p) m n = ∸-cancel-+-l p m n

∸-cancel-+-r : ∀ m p n → (m + p) ∸ (n + p) ＝ m ∸ n
∸-cancel-+-r m p n = ap² (_∸_) (+-comm m p) (+-comm n p) ∙ ∸-cancel-+-l p m n

+-cancel-∸-r : ∀ m n → (m + n) ∸ n ＝ m
+-cancel-∸-r m n = ∸-cancel-+-r m n 0

∸-+-assoc : ∀ m n p → n ∸ (m + p) ＝ (n ∸ m) ∸ p
∸-+-assoc  zero    n      p = refl
∸-+-assoc (suc m)  zero   p = ∸-zero-l p ⁻¹
∸-+-assoc (suc m) (suc n) p = ∸-+-assoc m n p

-- multiplication

·-absorb-r : (x : ℕ) → x · zero ＝ zero
·-absorb-r 0       = refl
·-absorb-r (suc x) = ·-absorb-r x

·-zero : (x y : ℕ) → x · y ＝ 0 → (x ＝ 0) ⊎ (y ＝ 0)
·-zero 0       _       _ = inl refl
·-zero (suc _) 0       _ = inr refl
·-zero (suc _) (suc _) p = false! p

·-suc-r : (x y : ℕ) → x · suc y ＝ x + x · y
·-suc-r 0       _ = refl
·-suc-r (suc x) y = ap suc $ ap (y +_) (·-suc-r x y) ∙ +-comm-assoc y x _

·-comm : (x y : ℕ) → x · y ＝ y · x
·-comm 0       y = (·-absorb-r y) ⁻¹
·-comm (suc x) y = ap (y +_) (·-comm x _) ∙ sym (·-suc-r y x)

·-id-l : (x : ℕ) → 1 · x ＝ x
·-id-l = +-zero-r

·-id-r : (x : ℕ) → x · 1 ＝ x
·-id-r x = ·-comm x 1 ∙ ·-id-l x

·-distrib-+-r : (x y z : ℕ) → (x + y) · z ＝ x · z + y · z
·-distrib-+-r 0       _ _ = refl
·-distrib-+-r (suc x) y z = ap (z +_) (·-distrib-+-r x y z) ∙ +-assoc z (x · z) (y · z)

·-distrib-+-l : (x y z : ℕ) → x · (y + z) ＝ x · y + x · z
·-distrib-+-l x y z = ·-comm x (y + z) ∙ ·-distrib-+-r y z x ∙ ap² _+_ (·-comm y x) (·-comm z x)

·-distrib-∸-r : (x y z : ℕ) → (x ∸ y) · z ＝ x · z ∸ y · z
·-distrib-∸-r  zero    y      z = ap (_· z) (∸-zero-l y) ∙ sym (∸-zero-l (y · z))
·-distrib-∸-r (suc x)  zero   z = refl
·-distrib-∸-r (suc x) (suc y) z = ·-distrib-∸-r x y z ∙ sym (∸-cancel-+-l z (x · z) (y · z))

·-distrib-∸-l : (x y z : ℕ) → x · (y ∸ z) ＝ x · y ∸ x · z
·-distrib-∸-l x y z = ·-comm x (y ∸ z) ∙ ·-distrib-∸-r y z x ∙ ap² _∸_ (·-comm y x) (·-comm z x)

·-assoc : (x y z : ℕ) → x · (y · z) ＝ x · y · z
·-assoc 0       _ _ = refl
·-assoc (suc x) y z = ap (y · z +_) (·-assoc x y z) ∙ sym (·-distrib-+-r y _ _)

·-cancel-r : ∀ m1 m2 n → m1 · n ＝ m2 · n → (m1 ＝ m2) ⊎ (n ＝ 0)
·-cancel-r  zero     zero    n e = inl refl
·-cancel-r  zero    (suc m2) n e = inr (+=0-2 n (m2 · n) (sym e) .fst)
·-cancel-r (suc m1)  zero    n e = inr (+=0-2 n (m1 · n) e .fst)
·-cancel-r (suc m1) (suc m2) n e = [ inl ∘ ap suc , inr ]ᵤ (·-cancel-r m1 m2 n (+-cancel-l n (m1 · n) (m2 · n) e))

·-cancel-l : ∀ m n1 n2 → m · n1 ＝ m · n2 → (n1 ＝ n2) ⊎ (m ＝ 0)
·-cancel-l m n1 n2 e = ·-cancel-r n1 n2 m (·-comm n1 m ∙ e ∙ ·-comm m n2)

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

iter-swap : {ℓ : Level} {A : 𝒰 ℓ}
         → (m n : ℕ) → (f : A → A) → (x : A)
         → iter m f (iter n f x) ＝ iter n f (iter m f x)
iter-swap m n f x = iter-add m n f x ⁻¹ ∙ ap (λ q → iter q f x) (+-comm m n) ∙ iter-add n m f x

iter-idem : {ℓ : Level} {A : 𝒰 ℓ}
        → (n : ℕ) → (f : A → A) → (x : A)
        → (∀ m → f (iter m f x) ＝ iter m f x)
        → iter n f x ＝ x
iter-idem  zero   f x fid = refl
iter-idem (suc n) f x fid = fid n ∙ iter-idem n f x fid

-- TODO can't use Injective because of cyclic dependencies
iter-inj : {ℓ : Level} {A : 𝒰 ℓ}
         → (n : ℕ) (f : A → A)
         → (∀ {x y} → f x ＝ f y → x ＝ y)
         → ∀ {x y} → iter n f x ＝ iter n f y → x ＝ y
iter-inj  zero   f inj {x} {y} e = e
iter-inj (suc n) f inj {x} {y} e = iter-inj n f inj (inj e)
