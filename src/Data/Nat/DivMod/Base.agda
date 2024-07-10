{-# OPTIONS --safe #-}
module Data.Nat.DivMod.Base where

open import Foundations.Base
open import Foundations.Equiv
open import Data.Empty
open import Data.Nat.Base renaming (div-helper to divₕ; mod-helper to modₕ)
open import Data.Nat.DivMod
open import Data.Nat.Order.Base
open import Data.Nat.Properties

-- order

a[modₕ]n<n : ∀ acc d n → modₕ acc (acc + n) d n ≤ acc + n
a[modₕ]n<n acc zero    n       = ≤-trans ≤-+-l $ subst (_≤ acc + n) (+-comm acc n) ≤-refl
a[modₕ]n<n acc (suc d) zero    = a[modₕ]n<n zero d (acc + 0)
a[modₕ]n<n acc (suc d) (suc n) =
  subst (λ q → modₕ (suc acc) q d n ≤ q) (sym (+-suc-r acc n)) $
  a[modₕ]n<n (suc acc) d n

m%n<n : ∀ m n → 0 < n → m % n < n
m%n<n m  zero   p = absurd (≮z p)
m%n<n m (suc n) _ = ≤≃<suc .fst (a[modₕ]n<n 0 m n)

m≤n⇒m%n≡m : ∀ m n → m ≤ n → m % suc n ＝ m
m≤n⇒m%n≡m m n m≤n =
  let (k , e) = ≤→Σ m n m≤n in
  ap (modₕ 0 n m) (sym e) ∙ a≤n⇒a[modₕ]n≡a 0 n m k

m<n⇒m%n≡m : ∀ m n → m < n → m % n ＝ m
m<n⇒m%n≡m m  zero   m<n = refl
m<n⇒m%n≡m m (suc n) m<n = m≤n⇒m%n≡m m n ((≤≃<suc ₑ⁻¹) .fst m<n)

m/n*n≤m : ∀ m n → (m / n) · n ≤ m
m/n*n≤m m    zero   = z≤
m/n*n≤m m n@(suc _) =
  ≤-trans ≤-+-r $
  ＝→≤ $ +-comm (m / n · n) (m % n) ∙ sym (m≡m%n+[m/n]*n m n)
