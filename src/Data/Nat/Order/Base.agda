{-# OPTIONS --safe #-}
module Data.Nat.Order.Base where

open import Meta.Prelude

open import Meta.Search.HLevel

open import Correspondences.Decidable
open import Correspondences.Wellfounded

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base as Reflects
open import Data.Sum.Base
open import Data.Sum.Path

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Nat.Order.Computational
  using ( _≤ᵇ_ ; _<ᵇ_ ; _≥ᵇ_ ; _>ᵇ_
        ; _≰ᵇ_ ; _≮ᵇ_ ; _≱ᵇ_ ; _≯ᵇ_
        )
open import Data.Nat.Path
open import Data.Nat.Properties
open import Data.Nat.Solver

private variable
  m n k : ℕ

infix 3 _≤_ _<_ _≥_ _>_
        _≰_ _≮_ _≱_ _≯_

opaque
  _≤_ _<_ : Corr _ (ℕ , ℕ) 0ℓ

  m ≤ n = Σ[ k ꞉ ℕ ] (m + k ＝ n)
  m < n = suc m ≤ n

_≥_ _>_ _≰_ _≮_ _≱_ _≯_ : Corr _ (ℕ , ℕ) 0ℓ

m ≥ n =   n ≤ m
m > n =   n < m
m ≰ n = ¬ m ≤ n
m ≮ n = ¬ m < n
m ≱ n = ¬ m ≥ n
m ≯ n = ¬ m > n


opaque
  unfolding _≤_ is-of-hlevel

  ≤-is-prop : is-prop (m ≤ n)
  ≤-is-prop (_ , p) (_ , q) = Σ-prop-path! (+-inj-l _ _ _ (p ∙ q ⁻¹))

  <-is-prop : is-prop (m < n)
  <-is-prop = ≤-is-prop

instance
  H-Level-≤ : H-Level (suc k) (m ≤ n)
  H-Level-≤ = hlevel-prop-instance ≤-is-prop

  H-Level-< : H-Level (suc k) (m < n)
  H-Level-< = hlevel-prop-instance <-is-prop

  decomp-hlevel-≤ : goal-decomposition (quote is-of-hlevel) (m ≤ n)
  decomp-hlevel-≤ = decomp (quote ≤-is-prop) []

  decomp-hlevel-< : goal-decomposition (quote is-of-hlevel) (m < n)
  decomp-hlevel-< = decomp (quote <-is-prop) []


-- Properties of order

opaque
  unfolding _≤_

  z≤ : 0 ≤ n
  z≤ = _ , refl

  s≤s : m ≤ n → suc m ≤ suc n
  s≤s = second (ap suc)

  ≤-peel : suc m ≤ suc n → m ≤ n
  ≤-peel = second suc-inj

  ≤-peel-unpeel : (p : suc m ≤ suc n) → s≤s (≤-peel p) ＝ p
  ≤-peel-unpeel (_ , _) = refl ,ₚ prop!

  ≤-refl : n ≤ n
  ≤-refl = 0 , nat!

  ≤-trans : m ≤ n → n ≤ k → m ≤ k
  ≤-trans {k} (δ₁ , p) (δ₂ , q)
    = δ₁ + δ₂
    , nat! ∙ subst (λ φ → φ + δ₂ ＝ k) (symₚ p) q

  ≤-antisym : m ≤ n → n ≤ m → m ＝ n
  ≤-antisym (0      , p) (_      , _) = sym (+-zero-r _) ∙ p
  ≤-antisym (suc _  , _) (0      , q) = sym q ∙ +-zero-r _
  ≤-antisym {m} (suc δ₁ , p) (suc δ₂ , q) = ⊥.rec $ suc≠zero {m = δ₁ + suc δ₂} $ +-inj-l m _ 0 $
       +-assoc m (suc δ₁) (suc δ₂) ∙ subst (λ φ → φ + suc δ₂ ＝ m) (sym p) q ∙ nat!

  ≤-suc-r : m ≤ n → m ≤ suc n
  ≤-suc-r = bimap suc λ p → nat! ∙ ap suc p

  ≤-ascend : n ≤ suc n
  ≤-ascend = 1 , nat!

  suc≰id : suc n ≰ n
  suc≰id (k , p) = id≠plus-suc {m = k} (sym p ∙ nat!)

  s≰z : suc n ≰ 0
  s≰z = suc≠zero ∘ snd

  ≤-subst : {a b c d : ℕ} → a ＝ b → c ＝ d → a ≤ c → b ≤ d
  ≤-subst a=b c=d = second $ subst² (λ u v → u + _ ＝ v) a=b c=d


-- Properties of strict order

opaque
  unfolding _<_

  <-irr : n ≮ n
  <-irr = (λ p → id≠plus-suc (sym p ∙ nat!)) ∘ snd

  s<s : m < n → suc m < suc n
  s<s = s≤s

  <-peel : suc m < suc n → m < n
  <-peel = ≤-peel

  <-weaken : (x y : ℕ) → x < y → x ≤ y
  <-weaken x y (δ , p) = suc δ , nat! ∙ p

  <-trans : m < n → n < k → m < k
  <-trans (δ₁ , p) (δ₂ , q)
    = suc (δ₁ + δ₂)
    , nat! ∙ subst (λ φ → suc (φ + δ₂) ＝ _) (symₚ p) q

  <-asym : ∀[ _<_ →̇ _≯_ ]
  <-asym {x = m} {x = n} (δ₁ , p) (δ₂ , q) = id≠plus-suc {n = n} {m = 1 + δ₂ + δ₁}
    (subst (λ φ → suc (φ + δ₁) ＝ n) (symₚ q) p ⁻¹ ∙ nat!)

  <-suc-r : m < n → m < suc n
  <-suc-r = ≤-suc-r

  <-suc-l : suc m < n → m < n
  <-suc-l (δ , p) = suc δ , nat! ∙ p

  <-ascend : n < suc n
  <-ascend = 0 , +-zero-r _

  ≮z : n ≮ 0
  ≮z = s≰z

  z<s : 0 < suc n
  z<s = _ , refl


-- Conversion

opaque
  unfolding _<_
  <→≤ : ∀[ _<_ →̇ _≤_ ]
  <→≤ = bimap suc (nat! ∙_)

  <→≠ : ∀[ _<_ →̇ _≠_ {A = ℕ} ]
  <→≠ m<n m=n = <-irr (subst (_ <_) (sym m=n) m<n)

  ≤→≯ : ∀[ _≤_ →̇ _≯_ ]
  ≤→≯ {x = m} {x = n} (δ₁ , p) (δ₂ , q) = id≠plus-suc {m} {δ₁ + δ₂} $
    subst (λ φ → suc (φ + δ₂) ＝ m) (symₚ p) q ⁻¹ ∙ nat!

  ≤→<⊎= : ∀[ _≤_ →̇ _<_ ⊎̇ _＝_ {A = ℕ} ]
  ≤→<⊎= (0     , p) = inr $ nat! ∙ p
  ≤→<⊎= (suc δ , p) = inl $ δ , nat! ∙ p

  <⊎=→≤ : ∀[ _<_ ⊎̇ _＝_ {A = ℕ} →̇ _≤_ ]
  <⊎=→≤ (inl m<n) = <→≤ m<n
  <⊎=→≤ (inr m=n) = subst (_≤ _) (sym m=n) ≤-refl

<→≱ : ∀[ _<_ →̇ _≱_ ]
<→≱ m<n m≥n = ≤→≯ m≥n m<n

≯→≤ : ∀[ _≯_ →̇ _≤_ ]
≯→≤ {0}     {_}     _ = z≤
≯→≤ {suc _} {0}     f = ⊥.rec $ f z<s
≯→≤ {suc _} {suc _} f = s≤s $ ≯→≤ (f ∘ s<s)

≱→< : ∀[ _≱_ →̇ _<_ ]
≱→< {_}     {0}     f = ⊥.rec $ f z≤
≱→< {0}     {suc _} _ = z<s
≱→< {suc m} {suc n} f = s<s $ ≱→< (f ∘ s≤s)

≤≃≯ : (m ≤ n) ≃ (m ≯ n)
≤≃≯ = prop-extₑ! ≤→≯ ≯→≤

<≃≱ : (m < n) ≃ (m ≱ n)
<≃≱ = prop-extₑ! <→≱ ≱→<

≤≃<⊎= : (m ≤ n) ≃ ((m < n) ⊎ (m ＝ n))
≤≃<⊎= = prop-extₑ hlevel! (disjoint-⊎-is-prop hlevel! hlevel! (<→≠ $ₜ²_)) ≤→<⊎= <⊎=→≤

module ≤≃≯   {m} {n} = Equiv (≤≃≯   {m} {n})
module <≃≱   {m} {n} = Equiv (<≃≱   {m} {n})
module ≤≃<⊎= {m} {n} = Equiv (≤≃<⊎= {m} {n})


-- Decidability

<-reflects : Reflects _<_ _<ᵇ_
<-reflects _       0       = ofⁿ ≮z
<-reflects 0       (suc _) = ofʸ z<s
<-reflects (suc m) (suc n) =
  Reflects.dmap s<s (_∘ <-peel) $ <-reflects m n

<-dec : Decidable _<_
<-dec = reflects→decidable {2} {P = _<_} <-reflects

≤-reflects : Reflects _≤_ _≤ᵇ_
≤-reflects 0       _       = ofʸ z≤
≤-reflects (suc _) 0       = ofⁿ s≰z
≤-reflects (suc m) (suc n) =
  Reflects.dmap s≤s (_∘ ≤-peel) $ ≤-reflects m n

≤-dec : Decidable _≤_
≤-dec = reflects→decidable {2} {P = _≤_} ≤-reflects

-- TODO use trichotomy
≤-split : Π[ _<_ ⊎̇ _>_ ⊎̇ _＝_ {A = ℕ} ]
≤-split m n with <-dec m n
... | yes m<n = inl m<n
... | no  m≮n with <-dec n m
... | yes n<m = inr $ inl n<m
... | no  n≮m = inr $ inr $ ≤-antisym (≤≃≯.from n≮m) (≤≃≯.from m≮n)

opaque
  unfolding _<_
  <-wf : Wf _<_
  <-wf n = go n n ≤-refl where
    go : (x y : ℕ) → .(y ≤ x) → Acc _<_ y
    go x       0       _ = acc $ λ _ <z → ⊥.rec $ ≮z <z
    go 0       (suc y) w = ⊥.rec′ (s≰z w)
    go (suc x) (suc y) w = acc λ x′ w′ →
      go x x′ (≤-trans (≤-peel w′) (≤-peel w))
