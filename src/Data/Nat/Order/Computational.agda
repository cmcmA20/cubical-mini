{-# OPTIONS --safe #-}
module Data.Nat.Order.Computational where

open import Meta.Prelude

open import Data.Bool.Base as Bool
open import Data.Dec.Base
open import Data.Empty.Base as ⊥
open import Data.Id.Inductive.Base
open import Data.Sum.Base
open import Data.Unit.Base

open import Data.Nat.Base
open import Data.Nat.Base public
  using (_<ᵇ_)

private variable
  m n k : ℕ

infix 3 _≤ᵇ_      _≥ᵇ_ _>ᵇ_
        _≰ᵇ_ _≮ᵇ_ _≱ᵇ_ _≯ᵇ_

_≤ᵇ_ _≥ᵇ_ _>ᵇ_ _≰ᵇ_ _≮ᵇ_ _≱ᵇ_ _≯ᵇ_ : ℕ → ℕ → Bool

m ≤ᵇ n =      m <ᵇ suc n
m ≥ᵇ n =      n ≤ᵇ m
m >ᵇ n =      n <ᵇ m
m ≰ᵇ n = not (m ≤ᵇ n)
m ≮ᵇ n = not (m <ᵇ n)
m ≱ᵇ n = not (m ≥ᵇ n)
m ≯ᵇ n = not (m >ᵇ n)

infix 3 _≤_ _<_ _≥_ _>_
        _≰_ _≮_ _≱_ _≯_

_≥_ _>_ _≰_ _≮_ _≱_ _≯_ : Corr _ (ℕ , ℕ) 0ℓ

_<_ : ℕ → ℕ → Type
m < n = is-true (m <ᵇ n)

_≤_ : ℕ → ℕ → Type
m ≤ n = is-true (m ≤ᵇ n)

m ≥ n =   n ≤ m
m > n =   n < m
m ≰ n = ¬ m ≤ n
m ≮ n = ¬ m < n
m ≱ n = ¬ m ≥ n
m ≯ n = ¬ m > n


-- Properties of strict order

<-trans : m < n → n < k → m < k
<-trans {0}     {suc n} {suc k} _ _ = tt
<-trans {suc m} {suc n} {suc k} p q = <-trans {m} {n} {k} p q

<-irr : ¬ m < m
<-irr {suc m} = <-irr {m}

<-asym : m < n → ¬ n < m
<-asym {0}     {suc n} _ x = x
<-asym {suc m} {suc n} p = <-asym {m} p

<-peel : suc m < suc n → m < n
<-peel = refl

<-suc-r : m < n → m < suc n
<-suc-r {0}             p = _
<-suc-r {suc m} {suc _} p = <-suc-r {m} p

<→s : m < n → Σ[ k ꞉ ℕ ] (n ＝ suc k)
<→s {m} {suc n} p = n , refl

opaque
  <-is-prop : is-prop (m < n)
  <-is-prop {0}     {suc _} _ _ = refl
  <-is-prop {suc m} {suc n} = <-is-prop {m} {n}

instance opaque
  <-is-of-hlevel : is-of-hlevel (suc k) (m < n)
  <-is-of-hlevel {m} {n} = is-prop→is-of-hlevel-suc (<-is-prop {m} {n})


-- Properties of order

z≤ : 0 ≤ n
z≤ = tt

s≤s : m ≤ n → suc m ≤ suc n
s≤s = refl

≤-peel : suc m ≤ suc n → m ≤ n
≤-peel = refl

≤-refl : n ≤ n
≤-refl {0}     = tt
≤-refl {suc n} = ≤-refl {n}

≤-trans : m ≤ n → n ≤ k → m ≤ k
≤-trans {0}     {_}             _ _ = tt
≤-trans {suc m} {suc n} {suc k} p q = ≤-trans {m} p q

≤-antisym : m ≤ n → n ≤ m → m ＝ n
≤-antisym {0}     {0}     _ _ = refl
≤-antisym {suc m} {suc n} p q = ap suc (≤-antisym p q)

≤-is-prop : is-prop (m ≤ n)
≤-is-prop {m} {n} = <-is-prop {m} {suc n}

≤-suc-r : m ≤ n → m ≤ suc n
≤-suc-r {0}     {_}     _ = tt
≤-suc-r {suc m} {suc n} p = ≤-suc-r {m} p

≤-ascend : n ≤ suc n
≤-ascend {n} = ≤-suc-r {n} (≤-refl {n})

≤-dec : (m n : ℕ) → Dec (m ≤ n)
≤-dec m n with m ≤ᵇ n
... | false = no  refl
... | true  = yes tt

suc≰id : ¬ suc n ≤ n
suc≰id {suc n} = suc≰id {n}

s≰z : suc n ≰ 0
s≰z {suc _} ()

≤-split : (m n : ℕ) → (m < n) ⊎ (n < m) ⊎ (m ＝ n)
≤-split m n with m <ᵇ n in p
... | true  = inl tt
... | false with n <ᵇ m in q
... | true  = inr $ inl tt
... | false = inr $ inr $ go m n
  (substⁱ is-true p)
  (substⁱ is-true q) where
    go : ∀ m n → ¬ (m < n) → ¬ (n < m) → m ＝ n
    go 0       0       _ _ = refl
    go 0       (suc _) p _ = ⊥.rec $ p tt
    go (suc _) 0       _ q = ⊥.rec $ q tt
    go (suc m) (suc n) p q = ap suc $ go m n p q
