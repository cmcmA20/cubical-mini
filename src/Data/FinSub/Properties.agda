{-# OPTIONS --safe #-}
module Data.FinSub.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind
open import Meta.Search.Discrete
open import Meta.Search.HLevel

open import Correspondences.Erased

open import Data.Empty.Base
open import Data.Nat.Order.Computational
open import Data.Nat.Path
open import Data.Nat.Instances.Discrete
import      Data.Sum.Base as ⊎
open ⊎

open import Data.FinSub.Base public
open import Data.Fin.Properties using ()
  renaming (fin-injective to finⁱ-injective)
open import Data.FinSub.Path

private variable
  ℓ : Level
  @0 m n : ℕ

opaque
  unfolding Fin index bound

  fin-is-set : is-set (Fin n)
  fin-is-set {n} = Σ-is-of-hlevel 2 hlevel! λ z → is-prop→is-set (∥-∥ᴱ-is-prop (≤-is-prop {suc z} {n}))

  strengthen : {n : ℕ} → Fin (suc n) → Fin (suc n) ⊎ Fin n
  strengthen (k , p) = go k p where
    go : {n : ℕ} (k : ℕ) → ∥ k < suc n ∥ᴱ → Fin (suc n) ⊎ Fin n
    go {0} k p = inl (k , p)
    go {suc n} 0 _ = inl fzero
    go {suc n} (suc k) ∣ p ∣ᴱ = ⊎.map fsuc fsuc $ go k ∣ p ∣ᴱ

  inject : m ≤ n → Fin m → Fin n
  inject {m} p (k , ∣ q ∣ᴱ) = k , ∣ ≤-trans {suc k} {m} q p ∣ᴱ

  fzero≠fsuc : {k : Fin m} → ¬ fzero ＝ fsuc k
  fzero≠fsuc {m} = suc≠zero ∘ sym ∘ ap (index {suc m})

  fsuc-inj : {k l : Fin m} → fsuc k ＝ fsuc l → k ＝ l
  fsuc-inj {m} {k} = ap pred′ where
    pred′ : Fin (suc m) → Fin m
    pred′ (0 , _) = k
    pred′ (suc k , ∣ p ∣ᴱ) = k , ∣ p ∣ᴱ

  fin-injective : {m n : ℕ} → Fin m ≃ Fin n → m ＝ n
  fin-injective f = finⁱ-injective $ (sub-fin≃finⁱ ₑ⁻¹) ∙ₑ f ∙ₑ sub-fin≃finⁱ

  fin-choice
    : ∀ n {A : Fin n → Type ℓ} {M}
        (let module M = Effect M)
    → ⦃ Bind M ⦄
    → (∀ x → M.₀ (A x)) → M.₀ (∀ x → A x)
  fin-choice 0 _ = pure λ()
  fin-choice (suc n) {A} k = do
    azero ← k fzero
    asuc  ← fin-choice n (k ∘ fsuc)
    pure λ where
      (0 , _) → azero
      (suc k , ∣ p ∣ᴱ) → asuc $ k , ∣ p ∣ᴱ

  opaque
    unfolding is-prop→pathP
    fin-ext-refl : {x : Fin n} → fin-ext {k₁ = x} refl ＝ refl {x = x}
    fin-ext-refl {n} = fin-is-set {n} _ _ _ refl
