{-# OPTIONS --safe #-}
module Data.Fin.Computational.Properties where

open import Foundations.Base hiding (_∙_)
open import Foundations.Equiv

open import Meta.Effect.Bind
open import Meta.Groupoid
open import Meta.Search.HLevel

open import Data.Empty.Base
open import Data.Nat.Order.Computational
open import Data.Nat.Path
open import Data.Sum.Base as ⊎

open import Data.Fin.Computational.Base public
open import Data.Fin.Inductive.Properties
  using (default≃inductive)
  renaming (fin-injective to finⁱ-injective)
open import Data.Fin.Computational.Path

private variable
  ℓ : Level
  @0 m n : ℕ

open Fin

fin-is-set : is-set (Fin n)
fin-is-set {n} = is-of-hlevel-≃ 2 (iso→equiv fin-iso)
  (Σ-is-of-hlevel 2 hlevel! λ z → is-prop→is-set (erased-is-prop (≤-is-prop {suc z} {n})))

strengthen : {n : ℕ} → Fin (suc n) → Fin (suc n) ⊎ Fin n
strengthen {0}     (mk-fin k {(b)})       = inl (mk-fin k {b})
strengthen {suc n} (mk-fin 0)             = inl fzero
strengthen {suc n} (mk-fin (suc k) {(b)}) = ⊎.dmap fsuc fsuc (strengthen (mk-fin k {b}))

inject : m ≤ n → Fin m → Fin n
inject {m} p (mk-fin k {erase q}) = mk-fin k {erase (≤-trans {suc k} {m} q p)}

fzero≠fsuc : {k : Fin m} → fzero ≠ fsuc k
fzero≠fsuc = suc≠zero ∘ sym ∘ ap index

fsuc-inj : {k l : Fin m} → fsuc k ＝ fsuc l → k ＝ l
fsuc-inj {m} {k} = ap pred′ where
  pred′ : Fin (suc m) → Fin m
  pred′ (mk-fin 0)       = k
  pred′ (mk-fin (suc k)) = mk-fin k

-- TODO too clunky, refactor this
fin-injective : {m n : ℕ} → Fin m ≃ Fin n → m ＝ n
fin-injective f = finⁱ-injective $ sub-fin≃finⁱ ⁻¹ ∙ f ∙ sub-fin≃finⁱ where
  sub-fin≃finⁱ : ∀ {n} → Fin n ≃ _
  sub-fin≃finⁱ = default≃computational ⁻¹ ∙ default≃inductive

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
    (mk-fin 0)       → azero
    (mk-fin (suc k)) → asuc (mk-fin k)

opaque
  unfolding is-prop→pathP
  fin-ext-refl : {x : Fin n} → fin-ext refl ＝ refl {x = x}
  fin-ext-refl = fin-is-set _ _ _ refl
