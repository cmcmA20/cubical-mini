{-# OPTIONS --safe #-}
module Data.Nat.Order.Inductive.Conversion where

open import Meta.Prelude

open import Data.Empty.Base
open import Data.Nat.Order.Inductive.Base
open import Data.Nat.Order.Inductive.Decidability
open import Data.Nat.Path
open import Data.Nat.Properties
open import Data.Sum.Base as ⊎
open import Data.Sum.Path as ⊎

private variable m n k : ℕ

=→≤ : ∀[ _＝_ {A = ℕ} →̇ _≤_ ]
=→≤ p = ≤-subst refl p refl

<→≤ : ∀[ _<_ →̇ _≤_ ]
<→≤ p = ≤-ascend ∙ p

<→≠ : ∀[ _<_ →̇ _≠_ {A = ℕ} ]
<→≠ {x = m} {x = n} m<n m=n = suc≰id (subst (_≤ n) (ap suc m=n) m<n)

≤≃≯ : (m ≤ n) ≃ (m ≯ n)
≤≃≯ = prop-extₑ! ≤→≯ ≯→≤ where
  ≤→≯ : ∀[ _≤_ →̇ _≯_ ]
  ≤→≯ (s≤s p) (s≤s q) = ≤→≯ p q

  ≯→≤ : ∀[ _≯_ →̇ _≤_ ]
  ≯→≤ {x = m} {x = n} f =
    [ (λ p → absurd $ f $ <→≤ p)
    , [ ≤-peel
      , (λ p → absurd $ f $ =→≤ p)
      ]ᵤ
    ]ᵤ $ ≤-split (suc n) m

≤≃<⊎= : (m ≤ n)
      ≃ (m < n) ⊎ (m ＝ n)
≤≃<⊎= = prop-extₑ (hlevel 1) (disjoint-⊎-is-prop! (<→≠ $ₜ²_)) ≤→<⊎= <⊎=→≤
  where
  ≤→<⊎= : ∀[ _≤_ →̇ _<_ ⊎̇ _＝_ {A = ℕ} ]
  ≤→<⊎= {x = 0}     {x = 0}     z≤      = inr refl
  ≤→<⊎= {x = 0}     {x = suc n} z≤      = inl (s≤s z≤)
  ≤→<⊎= {x = suc m} {x = suc n} (s≤s p) = ⊎.dmap s≤s (ap suc) $ ≤→<⊎= p

  <⊎=→≤ : ∀[ _<_ ⊎̇ _＝_ {A = ℕ} →̇ _≤_ ]
  <⊎=→≤ {x = m} {x = n} = [ <→≤ , =→≤ ]ᵤ

<≃≱ : (m < n) ≃ (m ≱ n)
<≃≱ = prop-extₑ! <→≱ ≱→< where
  <→≱ : ∀[ _<_ →̇ _≱_ ]
  <→≱ m<n m≥n = (≤≃≯ # m≥n)  m<n

  ≱→< : ∀[ _≱_ →̇ _<_ ]
  ≱→< p = ≤≃≯ ⁻¹ $ (p ∘ ≤-peel)

≤≃≤+l : (n ≤ k) ≃ (m + n ≤ m + k)
≤≃≤+l {n} {k} {m} = prop-extₑ! (ff m n k) (gg m n k)
  where
  ff : (a b c : ℕ) → b ≤ c → a + b ≤ a + c
  ff zero    b c p = p
  ff (suc a) b c p = s≤s (ff a b c p)

  gg : (a b c : ℕ) → a + b ≤ a + c → b ≤ c
  gg  zero   b c p = p
  gg (suc a) b c p = gg a b c (≤-peel p)

≤≃≤+r : (m ≤ n) ≃ (m + k ≤ n + k)
≤≃≤+r {m} {n} {k} = ≤≃≤+l ∙ prop-extₑ!
  (≤-subst (+-comm k m) (+-comm k n))
  (≤-subst (+-comm m k) (+-comm n k))

<≃<+l : (n < k) ≃ (m + n < m + k)
<≃<+l {n} {k} {m} = ≤≃≤+l ∙ prop-extₑ!
  (≤-subst (+-suc-r m n) refl)
  (≤-subst (+-suc-r m n ⁻¹) refl)

<≃<+r : (m < n) ≃ (m + k < n + k)
<≃<+r = ≤≃≤+r

<≃≤pred : 0 < n → (m < n) ≃ (m ≤ pred n)
<≃≤pred {n} {m} n0 =
  subst (λ q → m < q ≃ m ≤ʰ pred n) (suc-pred n n0 ⁻¹) (≤≃≤+l ⁻¹)
