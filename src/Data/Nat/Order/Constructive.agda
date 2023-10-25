{-# OPTIONS --safe #-}
module Data.Nat.Order.Constructive where

open import Foundations.Base
open import Foundations.HLevel
open import Foundations.Sigma

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Sum.Base
open import Data.Unit.Base

open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Nat.Properties

private variable
  m n k : ℕ

_≤_ : ℕ → ℕ → Type
m ≤ n = Σ[ k ꞉ ℕ ] (m + k ＝ n)

z≤ : 0 ≤ n
z≤ = _ , refl

s≤s : m ≤ n → suc m ≤ suc n
s≤s = second (ap suc)

≤-peel : suc m ≤ suc n → m ≤ n
≤-peel = second (ap pred)


_<_ : ℕ → ℕ → Type
m < n = suc m ≤ n
infix 3 _<_ _≤_

_≥_ : ℕ → ℕ → Type
m ≥ n = n ≤ m

_>_ : ℕ → ℕ → Type
m > n = n < m

-- Properties of order

≤-refl : n ≤ n
≤-refl = 0 , +-zero-r _

≤-trans : m ≤ n → n ≤ k → m ≤ k
≤-trans {m} (δ₁ , p) (δ₂ , q) = δ₁ + δ₂ , +-assoc m _ _ ∙ ap (_+ _) p ∙ q

≤-antisym : m ≤ n → n ≤ m → m ＝ n
≤-antisym (0      , p) (_      , _) = sym (+-zero-r _) ∙ p
≤-antisym (suc _  , _) (0      , q) = sym q ∙ +-zero-r _
≤-antisym {m} (suc δ₁ , p) (suc δ₂ , q) = ⊥.rec (suc≠zero $ +-inj-l m _ _ $
  +-assoc m _ _ ∙ subst (λ φ → φ + suc δ₂ ＝ m) (sym p) q ∙ sym (+-zero-r _))

opaque
  unfolding is-of-hlevel
  ≤-is-prop : is-prop (m ≤ n)
  ≤-is-prop (_ , p) (_ , q) = Σ-prop-path (λ _ → ℕ-is-set _ _) (+-inj-l _ _ _ (p ∙ sym q))

≤-suc-r : m ≤ n → m ≤ suc n
≤-suc-r = bimap suc (λ p → +-suc-r _ _ ∙ ap suc p)

≤-ascend : n ≤ suc n
≤-ascend = 1 , +-suc-r _ _ ∙ ap suc (+-zero-r _)

instance
  ≤-is-of-hlevel : is-of-hlevel (suc k) (m ≤ n)
  ≤-is-of-hlevel = is-prop→is-of-hlevel-suc ≤-is-prop

≤-dec : (m n : ℕ) → Dec (m ≤ n)
≤-dec 0       _       = yes z≤
≤-dec (suc _) 0       = no $ suc≠zero ∘ snd
≤-dec (suc m) (suc n) = Dec.map s≤s (_∘ ≤-peel) $ ≤-dec m n

sucn≰n : ¬ (suc n ≤ n)
sucn≰n = suc≠zero ∘ +-inj-l _ _ _ ∘ (+-suc-r _ _ ∙∙_∙∙ sym (+-zero-r _)) ∘ snd

¬sucn≤0 : ¬ (suc n ≤ 0)
¬sucn≤0 = suc≠zero ∘ snd

≤-split : (m n : ℕ) → (m < n) ⊎ (n < m) ⊎ (m ＝ n)
≤-split m n with ≤-dec (suc m) n
... | yes m<n = inl m<n
... | no  m≥n with ≤-dec (suc n) m
... | yes n<m = inr $ inl n<m
... | no  n≥m = inr $ inr (go m n m≥n n≥m) where
    go : ∀ m n → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ＝ n
    go 0       0         _ _ = refl
    go 0       (suc n) p _ = ⊥.rec (p $ s≤s z≤)
    go (suc m) 0       _ q = ⊥.rec (q $ s≤s z≤)
    go (suc m) (suc n) p q = ap suc $ go m n (p ∘ s≤s) (q ∘ s≤s)
