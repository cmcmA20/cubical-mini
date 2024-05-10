{-# OPTIONS --safe #-}
module Data.Fin.Computational.Properties where

open import Meta.Prelude

open import Meta.Effect.Bind

open import Data.Empty.Base
open import Data.Fin.Computational.Base public
open import Data.Fin.Inductive.Properties
  using (default≃inductive)
  renaming (fin-injective to finⁱ-injective)
open import Data.Fin.Computational.Path
open import Data.Nat.Order.Inductive.Base
open import Data.Nat.Order.Inductive.Decidability
open import Data.Nat.Path
open import Data.Reflects.Base
open import Data.Sum.Base as ⊎

private variable
  ℓ : Level
  @0 m n : ℕ

open Fin

strengthen : {n : ℕ} → Fin (suc n) → Fin (suc n) ⊎ Fin n
strengthen {0}     (mk-fin k {(b)})       = inl (mk-fin k {b})
strengthen {suc n} (mk-fin 0)             = inl fzero
strengthen {suc n} (mk-fin (suc k) {(b)}) = ⊎.dmap fsuc fsuc (strengthen (mk-fin k {b}))

inject : m ≤ n → Fin m → Fin n
inject {m} {n} p (mk-fin k {erase q}) = mk-fin k
  {erase (reflects-true (≤-reflects (suc k) n) (true-reflects (≤-reflects (suc k) m) q ∙ p))}

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
